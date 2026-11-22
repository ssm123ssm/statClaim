# Third-party software

StatClaim is MIT licensed. Dependencies keep their own licenses.
Lean 4 and Mathlib are Apache-2.0 licensed. They are fetched separately;
see their checked-out license files in the toolchain and `.lake/packages/mathlib`.
The VS Code extension bundles npm dependencies; its VSIX includes their
licenses in `ThirdPartyNotices.txt`. The web studio serves Pyodide
(Mozilla Public License 2.0), which includes CPython (Python Software Foundation
License); the site says so in `pyodide/NOTICE.txt`. Lockfiles record dependency versions.
