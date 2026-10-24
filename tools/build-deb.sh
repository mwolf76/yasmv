#!/bin/sh
#
# Build the yasmv Debian packages from a git tree.
#
# Usage: tools/build-deb.sh [TREE-ISH] [OUTPUT-DIR]
#
# Packs TREE-ISH (default HEAD) as the yasmv upstream tarball, fetches the
# pinned CaDiCaL release as the cadical component, builds unsigned source
# and binary packages, and runs lintian. Output goes to OUTPUT-DIR (default
# build-deb/). The build dependencies in debian/control must be installed.

set -eu

cd "$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"

tree=${1:-HEAD}
out=${2:-build-deb}

# debian/rules stamps this tarball with the pinned revision, so only the
# verified release may be used.
cadical_url=https://github.com/arminbiere/cadical/archive/refs/tags/rel-3.0.1.tar.gz
cadical_sha256=0a8ea563b5a25f5aa064634814edab45cc0e45111ea0f5d412a565f806fd7e11

version=$(git show "$tree:debian/changelog" | dpkg-parsechangelog -l - -S Version)
upstream=${version%-*}
source=yasmv-$upstream

mkdir -p "$out"
out=$(cd "$out" && pwd)

# Single-threaded xz keeps the tarball identical across machines.
git archive --format=tar --prefix="$source/" "$tree" ':(exclude)debian' \
    | xz -T1 -6 > "$out/yasmv_$upstream.orig.tar.xz"

cadical=$out/yasmv_$upstream.orig-cadical.tar.gz
if [ ! -f "$cadical" ]; then
    curl -fsSL -o "$cadical.part" "$cadical_url"
    mv "$cadical.part" "$cadical"
fi
echo "$cadical_sha256  $cadical" | sha256sum -c --quiet -

rm -rf "${out:?}/$source"
tar -xJf "$out/yasmv_$upstream.orig.tar.xz" -C "$out"
mkdir "$out/$source/cadical"
tar -xzf "$cadical" -C "$out/$source/cadical" --strip-components=1
git archive --format=tar "$tree" debian | tar -x -C "$out/$source"

(cd "$out/$source" && dpkg-buildpackage -us -uc)
# The packaging follows Debian conventions on every distribution.
lintian --profile debian "$out/yasmv_${version}"_*.changes
