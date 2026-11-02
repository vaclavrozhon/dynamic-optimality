#!/usr/bin/env bash
set -euo pipefail

# Official elan v4.2.4 Linux x86-64 release; the checksum is published in
# https://api.github.com/repos/leanprover/elan/releases/tags/v4.2.4.
: "${RUNNER_TEMP:?This installer expects a GitHub Actions runner}"
: "${GITHUB_PATH:?The runner must provide GITHUB_PATH}"
elan_install_dir="${RUNNER_TEMP}/dynamic-optimality-elan"
mkdir -p "$elan_install_dir"
curl --fail --location --retry 3 --proto '=https' --tlsv1.2 \
  https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz \
  --output "$elan_install_dir/elan.tar.gz"
printf '%s  %s\n' \
  42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63 \
  "$elan_install_dir/elan.tar.gz" | sha256sum --check -
tar -xzf "$elan_install_dir/elan.tar.gz" -C "$elan_install_dir"
"$elan_install_dir/elan-init" -y --no-modify-path --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
printf '%s\n' "$HOME/.elan/bin" >> "$GITHUB_PATH"
elan toolchain install "$(cat lean-toolchain)"
lean --version
lake --version
