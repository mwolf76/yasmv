# Debian Packaging for yasmv

This directory contains the necessary files to build Debian packages for yasmv.

## Building the Package Locally

### Prerequisites

Install the required build dependencies:

```bash
sudo apt-get update
sudo apt-get install -y \
  build-essential \
  debhelper \
  devscripts \
  libboost-all-dev \
  libjsoncpp-dev \
  antlr3 \
  libantlr3c-dev \
  minisat \
  zlib1g-dev \
  libyaml-cpp-dev \
  openjdk-11-jdk \
  autoconf \
  libtool \
  llvm-dev \
  libclang-dev \
  clang
```

### Building

From the project root directory:

```bash
# Set up the build environment
./setup.sh

# Build the package
dpkg-buildpackage -us -uc -b
```

The resulting .deb file will be created in the parent directory.

### Installation

```bash
sudo dpkg -i ../yasmv_*.deb
sudo apt-get install -f  # Fix any dependency issues
```

## Automated Builds

The project includes GitHub Actions workflows for:

1. **Testing Debian builds** on pull requests (`.github/workflows/test-deb-build.yml`)
2. **Creating releases** with Debian packages (`.github/workflows/release-deb.yml`)

### Test Builds

Every pull request that modifies packaging files or source code triggers a test build on:
- Ubuntu 22.04 LTS (Jammy)
- Ubuntu 24.04 LTS (Noble)

### Release Builds

When a version tag (e.g., `v1.0.0`) is pushed, the release workflow:
1. Builds packages for both Ubuntu versions
2. Creates a GitHub release
3. Attaches the .deb files to the release

To trigger a release:
```bash
git tag v1.0.0
git push origin v1.0.0
```

## Package Structure

- `control` - Package metadata and dependencies
- `rules` - Build instructions
- `changelog` - Version history
- `compat` - Debhelper compatibility level
- `copyright` - License information
- `source/format` - Source package format
- `yasmv.manpages` - Manual pages to install