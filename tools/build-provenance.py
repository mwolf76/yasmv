#!/usr/bin/env python3
"""Record the toolchain and the exact packaged arithmetic fragment inventory."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def command(*args):
    try:
        result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True, timeout=10)
        return {"status": result.returncode, "output": result.stdout.strip(),
                "diagnostic": result.stderr.strip()}
    except (OSError, subprocess.TimeoutExpired) as error:
        return {"unavailable": str(error)}


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    fragments = [{"path": str(path.relative_to(ROOT)), "sha256": digest(path),
                  "bytes": path.stat().st_size}
                 for path in sorted((ROOT / "microcode").glob("*.json"))]
    report = {
        "revision": command("git", "rev-parse", "HEAD"),
        "working_tree": command("git", "status", "--short"),
        "platform": platform.platform(),
        "compiler": command("c++", "--version"),
        "configure": command("./config.status", "--config"),
        "linked_libraries": command("ldd", "./yasmv"),
        "packages": command("dpkg-query", "-W", "minisat", "libantlr3c-dev", "libjsoncpp-dev", "libboost-dev"),
        "fragment_count": len(fragments),
        "fragment_manifest_sha256": hashlib.sha256(json.dumps(fragments, sort_keys=True).encode()).hexdigest(),
        "fragments": fragments,
    }
    output = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(output)
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
