# Lean verification artifacts

The `Lean verification` workflow runs on pushes to every branch and can be
started manually. It installs the toolchain in `lean-toolchain`, downloads
Mathlib's pinned cache, builds every registered local module through the graph
exporter, runs `make audit`, and packages the graph. Lake uses four worker
threads. Build commands run sequentially; dependency sources are not changed.

The workflow uploads two artifacts, identified by the source commit:

- `lean-verification-<commit>` contains the standalone HTML graph, its summary,
  the complete graph JSON, module inventory, and build/audit/export logs. Logs
  are uploaded even when verification fails; a failed run is not a certificate.
- `lean-build-<commit>` is uploaded whenever a local build cache was produced,
  including after failed verification. It contains `project-build.tar.gz`,
  `project-build.json`, and `SHA256SUMS`. The metadata explicitly labels the
  verification status `passed` or `partial`. The
  archive contains only the root `.lake/build` directory; Mathlib and other
  dependency directories under `.lake/packages` are excluded.

To reuse the compiled local artifacts, first check the workflow result and the
metadata's verification status. A partial cache can save recompilation after a
failure, but provides no evidence that the whole project passes verification.
Use Linux x86-64, the same Lean toolchain and pinned dependencies, and the source
commit recorded in `project-build.json`. That file also records the source and
configuration fingerprints. From the downloaded cache artifact directory,
verify the archive:

```sh
sha256sum --check SHA256SUMS
```

Then, from the matching repository checkout, obtain dependency artifacts and
unpack the local cache, replacing the example path with the downloaded archive:

```sh
lake exe cache get
tar -xzf /path/to/project-build.tar.gz
flock /tmp/dynamic-optimality-lean-build.lock make audit
```

Stop any existing Lean build before restoring a cache. Restoring cached files
does not itself establish that an audit has passed on the local machine. After
restoring a partial cache, rerun the full workflow's checks, including the graph
exporter's explicit build of every registered module.

The workflow pins the official [checkout v7.0.1](https://github.com/actions/checkout/releases/tag/v7.0.1)
and [upload-artifact v7.0.2](https://github.com/actions/upload-artifact/releases/tag/v7.0.2)
actions by commit. The installer pins the official
[elan v4.2.4 release](https://github.com/leanprover/elan/releases/tag/v4.2.4)
and verifies the published archive checksum before running it.
