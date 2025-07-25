#!/bin/bash
#
# Version bumping script for yasmv
# Copyright (C) 2025 yasmv project
#
# This script bumps the version number in configure.ac and creates
# a git commit with the version change.
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CONFIGURE_AC="$PROJECT_ROOT/configure.ac"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

usage() {
    cat << EOF
Usage: $0 [OPTIONS]

Bump version number in yasmv project.

OPTIONS:
    --major         Bump major version (x.y.z -> (x+1).0.0)
    --minor         Bump minor version (x.y.z -> x.(y+1).0)
    --patch         Bump patch version (x.y.z -> x.y.(z+1))
    --to VERSION    Set version to specific value (e.g., --to 1.2.3)
    --dry-run       Show what would be changed without making changes
    --no-commit     Don't create git commit after version bump
    -h, --help      Show this help message

EXAMPLES:
    $0 --patch              # 0.0.9 -> 0.0.10
    $0 --minor              # 0.0.9 -> 0.1.0
    $0 --major              # 0.0.9 -> 1.0.0
    $0 --to 2.1.0           # Set version to 2.1.0
    $0 --patch --dry-run    # Show what patch bump would do
    $0 --minor --no-commit  # Bump minor version without git commit

EOF
}

log_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

get_current_version() {
    grep "AC_INIT" "$CONFIGURE_AC" | sed -n 's/AC_INIT(\[yasmv\], \[\([^]]*\)\],.*/\1/p'
}

validate_version() {
    local version="$1"
    if ! [[ "$version" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
        log_error "Invalid version format: $version (expected: x.y.z)"
        return 1
    fi
}

bump_version() {
    local current="$1"
    local bump_type="$2"
    local target="$3"
    
    if [[ -n "$target" ]]; then
        validate_version "$target"
        echo "$target"
        return
    fi
    
    IFS='.' read -r major minor patch <<< "$current"
    
    case "$bump_type" in
        major)
            echo "$((major + 1)).0.0"
            ;;
        minor)
            echo "$major.$((minor + 1)).0"
            ;;
        patch)
            echo "$major.$minor.$((patch + 1))"
            ;;
        *)
            log_error "Unknown bump type: $bump_type"
            exit 1
            ;;
    esac
}

update_configure_ac() {
    local old_version="$1"
    local new_version="$2"
    local dry_run="$3"
    
    if [[ "$dry_run" == "true" ]]; then
        log_info "Would change version in configure.ac: $old_version -> $new_version"
        return
    fi
    
    # Create backup
    cp "$CONFIGURE_AC" "$CONFIGURE_AC.bak"
    
    # Update version
    sed -i "s/AC_INIT(\[yasmv\], \[$old_version\],/AC_INIT([yasmv], [$new_version],/" "$CONFIGURE_AC"
    
    # Verify change was made
    local updated_version=$(get_current_version)
    if [[ "$updated_version" != "$new_version" ]]; then
        log_error "Failed to update version in configure.ac"
        mv "$CONFIGURE_AC.bak" "$CONFIGURE_AC"
        exit 1
    fi
    
    rm "$CONFIGURE_AC.bak"
    log_info "Updated configure.ac: $old_version -> $new_version"
}

create_git_commit() {
    local version="$1"
    local dry_run="$2"
    local no_commit="$3"
    
    if [[ "$no_commit" == "true" ]]; then
        log_info "Skipping git commit (--no-commit specified)"
        return
    fi
    
    if [[ "$dry_run" == "true" ]]; then
        log_info "Would create git commit: 'Bump version to $version'"
        return
    fi
    
    # Check if we're in a git repository
    if ! git rev-parse --git-dir > /dev/null 2>&1; then
        log_warn "Not in a git repository, skipping commit"
        return
    fi
    
    # Check if there are changes to commit
    if ! git diff --quiet "$CONFIGURE_AC"; then
        git add "$CONFIGURE_AC"
        git commit -m "Bump version to $version

🤖 Generated with [Claude Code](https://claude.ai/code)

Co-Authored-By: Claude <noreply@anthropic.com>"
        log_info "Created git commit for version $version"
    else
        log_warn "No changes to commit"
    fi
}

main() {
    local bump_type=""
    local target_version=""
    local dry_run="false"
    local no_commit="false"
    
    # Parse arguments
    while [[ $# -gt 0 ]]; do
        case $1 in
            --major)
                bump_type="major"
                shift
                ;;
            --minor)
                bump_type="minor"
                shift
                ;;
            --patch)
                bump_type="patch"
                shift
                ;;
            --to)
                target_version="$2"
                shift 2
                ;;
            --dry-run)
                dry_run="true"
                shift
                ;;
            --no-commit)
                no_commit="true"
                shift
                ;;
            -h|--help)
                usage
                exit 0
                ;;
            *)
                log_error "Unknown option: $1"
                usage
                exit 1
                ;;
        esac
    done
    
    # Validate arguments
    if [[ -z "$bump_type" && -z "$target_version" ]]; then
        log_error "Must specify either --major, --minor, --patch, or --to VERSION"
        usage
        exit 1
    fi
    
    if [[ -n "$bump_type" && -n "$target_version" ]]; then
        log_error "Cannot specify both bump type and target version"
        usage
        exit 1
    fi
    
    # Check if configure.ac exists
    if [[ ! -f "$CONFIGURE_AC" ]]; then
        log_error "configure.ac not found at: $CONFIGURE_AC"
        exit 1
    fi
    
    # Get current version
    local current_version=$(get_current_version)
    if [[ -z "$current_version" ]]; then
        log_error "Could not determine current version from configure.ac"
        exit 1
    fi
    
    log_info "Current version: $current_version"
    
    # Calculate new version
    local new_version
    if [[ -n "$target_version" ]]; then
        validate_version "$target_version"
        new_version="$target_version"
    else
        new_version=$(bump_version "$current_version" "$bump_type" "$target_version")
    fi
    
    log_info "New version: $new_version"
    
    # Check if version actually changed
    if [[ "$current_version" == "$new_version" ]]; then
        log_warn "Version unchanged: $current_version"
        exit 0
    fi
    
    # Update configure.ac
    update_configure_ac "$current_version" "$new_version" "$dry_run"
    
    # Create git commit
    create_git_commit "$new_version" "$dry_run" "$no_commit"
    
    if [[ "$dry_run" == "false" ]]; then
        log_info "Version successfully updated to $new_version"
        log_info "Next steps:"
        log_info "  1. Run './setup.sh && make' to rebuild with new version"
        log_info "  2. Run tests to ensure everything works: 'make test'"
        log_info "  3. Push changes if satisfied: 'git push'"
    fi
}

main "$@"