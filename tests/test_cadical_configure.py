#!/usr/bin/env python3
"""Exercise the real configure macro with redirected output and a terminal."""
import errno
import os
from pathlib import Path
import subprocess
import tempfile
import threading
import unittest

ROOT = Path(__file__).resolve().parents[1]
REVISION = 'c60730422e758ef1cebe7aeddf2dda31c996bf04'

# Mirror CaDiCaL's process-start terminal detection, before main can freopen
# stdout. This fixture needs no downloaded solver or pre-existing local build.
HEADER = r'''
#include <cstdio>
#include <unistd.h>
#include <tracer.hpp>
namespace CaDiCaL {
inline const bool colors = isatty(STDOUT_FILENO);
struct Terminator { virtual bool terminate() = 0; virtual ~Terminator() = default; };
struct Solver {
    static const char *version() { return "@VERSION@"; }
    static const char *signature() { return "cadical-3.0.1-c607304"; }
    static void build(FILE *file, const char *) {
        std::fprintf(file, "%sVersion %s3.0.1%s @REVISION@%s\n",
                     colors ? "\033[0;35m" : "", colors ? "\033[0m" : "",
                     colors ? "\033[0;35m" : "", colors ? "\033[0m" : "");
    }
    bool set(const char *, int) { return true; }
    void connect_terminator(Terminator *) {}
    void disconnect_terminator() {}
    Tracer *tracer = nullptr;
    void connect_proof_tracer(Tracer *t, bool) { tracer = t; }
    bool disconnect_proof_tracer(Tracer *) { tracer = nullptr; return true; }
    void conclude() {}
    int declare_one_more_variable() { return 1; }
    void freeze(int) {}
    void melt(int) {}
    void add(int lit) { if (!lit && tracer) tracer->add_original_clause(1, false, {1}, false); }
    bool limit(const char *, int) { return true; }
    int assumed = 0;
    void assume(int value) { assumed = value; }
    int solve() { int result = assumed ? 20 : 10; assumed = 0; return result; }
    int val(int) { return 1; }
    bool failed(int) { return true; }
    long get_statistic_value(const char *) { return 0; }
};
}
'''

TRACER = r'''
#pragma once
#include <cstdint>
#include <vector>
namespace CaDiCaL {
struct Tracer {
    virtual ~Tracer() = default;
    virtual void add_original_clause(int64_t, bool, const std::vector<int>&, bool) {}
    virtual void add_derived_clause(int64_t, bool, int, const std::vector<int>&,
                                     const std::vector<int64_t>&) {}
};
}
'''


class ConfigureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source_directory = tempfile.TemporaryDirectory(prefix='cadical-configure-')
        cls.addClassCleanup(cls.source_directory.cleanup)
        cls.source = Path(cls.source_directory.name)
        (cls.source / 'configure.ac').write_text(
            'AC_INIT([cadical-configure-test], [1])\nAC_PROG_CXX\n' +
            (ROOT / 'm4/cadical.m4').read_text() + '\nAC_CADICAL\nAC_OUTPUT\n')
        subprocess.run(['autoconf'], cwd=cls.source, capture_output=True, check=True)

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix='cadical-configure-case-')
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name)
        self.prefix = self.path / 'prefix'
        (self.prefix / 'include').mkdir(parents=True)
        (self.prefix / 'lib').mkdir()
        (self.prefix / 'include/tracer.hpp').write_text(TRACER)
        subprocess.run(['ar', 'cr', str(self.prefix / 'lib/libcadical.a')], check=True)

    def configure(self, *, terminal, revision=REVISION, version='3.0.1'):
        (self.prefix / 'include/cadical.hpp').write_text(
            HEADER.replace('@REVISION@', revision).replace('@VERSION@', version))
        command = [str(self.source / 'configure'),
                   '--with-cadical-prefix=' + str(self.prefix), 'CXXFLAGS=-std=c++20']
        if not terminal:
            result = subprocess.run(command, cwd=self.path, capture_output=True,
                                    text=True, timeout=60)
            return result.returncode, result.stdout + result.stderr

        master, slave = os.openpty()
        output = []

        def read_terminal():
            while True:
                try:
                    data = os.read(master, 4096)
                except OSError as error:
                    if error.errno == errno.EIO:
                        break
                    raise
                if not data:
                    break
                output.append(data)

        reader = threading.Thread(target=read_terminal, daemon=True)
        reader.start()
        try:
            result = subprocess.run(command, cwd=self.path, stdin=subprocess.DEVNULL,
                                    stdout=slave, stderr=slave, timeout=60)
        finally:
            os.close(slave)
            reader.join(timeout=5)
            os.close(master)
        self.assertFalse(reader.is_alive(), 'terminal reader did not finish')
        return result.returncode, b''.join(output).decode(errors='replace')

    def test_valid_revision_with_redirected_output(self):
        status, output = self.configure(terminal=False)
        self.assertEqual(status, 0, output)

    def test_valid_revision_with_terminal_output(self):
        status, output = self.configure(terminal=True)
        self.assertEqual(status, 0, output)

    def test_wrong_full_revision_is_rejected(self):
        for terminal in (False, True):
            with self.subTest(terminal=terminal):
                status, output = self.configure(terminal=terminal,
                                                revision='c607304' + '0' * 33)
                self.assertNotEqual(status, 0)
                self.assertIn('required full build revision', output)

    def test_missing_full_revision_is_rejected(self):
        for terminal in (False, True):
            with self.subTest(terminal=terminal):
                status, output = self.configure(terminal=terminal, revision='')
                self.assertNotEqual(status, 0)
                self.assertIn('required full build revision', output)

    def test_wrong_version_is_rejected(self):
        status, output = self.configure(terminal=True, version='3.0.2')
        self.assertNotEqual(status, 0)
        self.assertIn('API/version check failed', output)

    def test_missing_proof_header_is_rejected(self):
        (self.prefix / 'include/tracer.hpp').unlink()
        status, output = self.configure(terminal=False)
        self.assertNotEqual(status, 0)
        self.assertIn('Matching pinned tracer.hpp not found', output)

    def test_incompatible_proof_header_is_rejected(self):
        (self.prefix / 'include/tracer.hpp').write_text(
            TRACER.replace('int64_t, bool, int,', 'int64_t, bool,'))
        status, output = self.configure(terminal=False)
        self.assertNotEqual(status, 0)
        self.assertIn('API/version check failed', output)


if __name__ == '__main__':
    unittest.main()
