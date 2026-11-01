# R212 proof handoff, revision 1 — frozen incomplete

Producer `/root/abstract_simple_sub_core_r211`; effective model/effort UNKNOWN.
Resumed UTC 2026-11-01T19:21:41.094227+00:00 under frozen contract
`dbe1e1f2b99960b0503d8f1eb65608f811045901416333a8b85030bc5181e7c9` and exact artifact manifest
`b162fbde8a83096f5bd2e5e9efe076ce07e7cfa8306e27ab551e46f1d359e1f2`.
Contract/manifest, all 12 module hashes, 3 tool hashes, 104 artifact statuses, and all 15 R211 pins matched.
One sequential build owner, CPU affinity restricted to one available CPU, LEAN_NUM_THREADS=1; project -j1/-M1024 retained.

R211 original-source audit and unchanged parent/quantifier map: `abstract-simple-sub-core-r211-proof.md`
SHA `5867c1c1eaddee9a2e719cbf94ec108fe5ce9453d2a3f38bbe59208f0aa9ec5c`.
No source-scope or theorem change is authorized by dependency generation.

Baseline sizes: `{"du_allocated": 103170048, "du_apparent": 101833211, "files": 448, "regular_allocated": 103112704, "regular_apparent": 101833211}`.
Manifest allocated baseline sums regular-file blocks; du includes directory blocks.
Earlier read-only preflight equality assertion failed at du_allocated 103170048 vs manifest regular_allocated 103112704;
primary confirmed measurement-method difference, no byte/hash/status mismatch.

## Sequential OLean build receipts

### Contracts

Command (cwd `notes/theory/lean`):

```sh
env LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR= /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache --fail-fast build +YulangClosure.Contracts:olean
```

Before: `{"du_allocated": 103170048, "du_apparent": 101833211, "files": 448, "regular_allocated": 103112704, "regular_apparent": 101833211}`.
After: `{"du_allocated": 103170048, "du_apparent": 101833211, "files": 448, "regular_allocated": 103112704, "regular_apparent": 101833211}`.
Elapsed 0.528 s; aggregate 0.528 s; exit 0; timeout False.

```text
Build completed successfully (2 jobs).

```

Created files (SHA-256):

None.

Modified/deleted existing files: `[]`.
Unexpected created paths: `[]`.

### SimpleSubConstraintSyntax

Command (cwd `notes/theory/lean`):

```sh
env LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR= /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache --fail-fast build +YulangClosure.SimpleSubConstraintSyntax:olean
```

Before: `{"du_allocated": 103170048, "du_apparent": 101833211, "files": 448, "regular_allocated": 103112704, "regular_apparent": 101833211}`.
After: `{"du_allocated": 104554496, "du_apparent": 103190801, "files": 456, "regular_allocated": 104497152, "regular_apparent": 103190801}`.
Elapsed 2.942 s; aggregate 3.470 s; exit 0; timeout False.

```text
✔ [3/3] Built YulangClosure.SimpleSubConstraintSyntax (2.9s)
Build completed successfully (3 jobs).

```

Created files (SHA-256):

* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubConstraintSyntax.c` — `04536a37874d98abcc2eefaa236c5876a4c11ccca3c5b813fc6b89de968a03dc`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubConstraintSyntax.c.hash` — `71f994ea300ce86bed7dd1aacee11fba6dde40769d10b2a879f369656d47ee96`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubConstraintSyntax.setup.json` — `ec2458086ce97cbc7c756660d3b8b1e44c21dca44713b8cf328797b695ca3a4a`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubConstraintSyntax.ilean` — `90f4ac073da08bb5a90caf94cd384202e2bf06cd1ead074e18af8c26a0dff19f`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubConstraintSyntax.ilean.hash` — `62b166914821f3368e3f9d96edd6a786c53d669ccc6a6271244311318b8ba833`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubConstraintSyntax.olean` — `5b9fe4a503d9b1f4445cdaafb811ecde9f0c5f2844aec8ed7808dee6d86c6ba3`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubConstraintSyntax.olean.hash` — `d48fc2dedde2c8390654f756b902139078a2decf8a00a1480ec6ccfb618e116e`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubConstraintSyntax.trace` — `d1b6405c347672c04985f1d83952f27576667376ed8930ee6eacd99ed775a8c6`

Modified/deleted existing files: `[]`.
Unexpected created paths: `[]`.

### SimpleSubConstraintSoundness

Command (cwd `notes/theory/lean`):

```sh
env LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR= /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache --fail-fast build +YulangClosure.SimpleSubConstraintSoundness:olean
```

Before: `{"du_allocated": 104554496, "du_apparent": 103190801, "files": 456, "regular_allocated": 104497152, "regular_apparent": 103190801}`.
After: `{"du_allocated": 105779200, "du_apparent": 104392596, "files": 464, "regular_allocated": 105721856, "regular_apparent": 104392596}`.
Elapsed 1.239 s; aggregate 4.709 s; exit 0; timeout False.

```text
✔ [4/4] Built YulangClosure.SimpleSubConstraintSoundness (1.1s)
Build completed successfully (4 jobs).

```

Created files (SHA-256):

* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubConstraintSoundness.c` — `a26dba5bf26044c44cc1039e9bb8d6cbf7ba99fc48731147056359e91214470e`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubConstraintSoundness.c.hash` — `6888d297144f81e9222f9d82e15f289b818d7b18bb79f469524579ca25ea1932`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubConstraintSoundness.setup.json` — `c0636fc46e47176f92c866adfca253df2034c63f013c081555e5c02867854a37`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubConstraintSoundness.ilean` — `2ffb3373b2f3a4370ef26e6aa0ad0eff4f018949fcb72e99c05864ea80af6ed4`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubConstraintSoundness.ilean.hash` — `043e65b808684ce6e3c858201853810b7abc5ab6f2939042150398ad7b9e0149`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubConstraintSoundness.olean` — `9d9f68e3bacb8a34b366eb4b9286b8c549b34125d5253b63d2814162bc157cc8`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubConstraintSoundness.olean.hash` — `5e825a97f57f401f4c0520f93c8ef8c63d289de536e29ac7c65a1f4874471546`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubConstraintSoundness.trace` — `6012acf09d23e8a35eca55632049e0f20a58f684fde7f10e7d635a80c30de99e`

Modified/deleted existing files: `[]`.
Unexpected created paths: `[]`.

### SimpleSubRegularSolutions

Command (cwd `notes/theory/lean`):

```sh
env LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR= /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache --fail-fast build +YulangClosure.SimpleSubRegularSolutions:olean
```

Before: `{"du_allocated": 105779200, "du_apparent": 104392596, "files": 464, "regular_allocated": 105721856, "regular_apparent": 104392596}`.
After: `{"du_allocated": 108736512, "du_apparent": 107322154, "files": 472, "regular_allocated": 108675072, "regular_apparent": 107322154}`.
Elapsed 1.545 s; aggregate 6.254 s; exit 0; timeout False.

```text
✔ [4/4] Built YulangClosure.SimpleSubRegularSolutions (1.5s)
Build completed successfully (4 jobs).

```

Created files (SHA-256):

* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubRegularSolutions.c` — `b8534e86391ce21ec324b6d142e8ffd59c4b76d5878a37b8a60ae144fcaaceb2`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubRegularSolutions.c.hash` — `8549b960abdfddc20760369d766fd3f7a93c5d3ee03cab46b3e6a9a235366ebc`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubRegularSolutions.setup.json` — `15f1c1472de2330428deedc661a12e9241ee998be62f9f068ea6081fba6b69b0`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubRegularSolutions.ilean` — `f92134398341b972b78f36f99ef6c23498afb9875d427c24864510bf2328e271`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubRegularSolutions.ilean.hash` — `80ef90a7f1f937f8903af2784aac387a74ccdf248da79b7cfbbf46a1c8fb5fb4`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubRegularSolutions.olean` — `ac30922e386fe2ab7fa041e921898f5e706e7db7d55d26b4b1cad161dc705f10`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubRegularSolutions.olean.hash` — `b6eb88c43713126973207d314b48820b07f6a07ec55777185ca9d850ab353848`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubRegularSolutions.trace` — `0557684e60788db3e03d617bb0d41295f909a143377bfc8631ef3e693844769c`

Modified/deleted existing files: `[]`.
Unexpected created paths: `[]`.

### SimpleSubRegularConstraintSoundness

Command (cwd `notes/theory/lean`):

```sh
env LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR= /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache --fail-fast build +YulangClosure.SimpleSubRegularConstraintSoundness:olean
```

Before: `{"du_allocated": 108736512, "du_apparent": 107322154, "files": 472, "regular_allocated": 108675072, "regular_apparent": 107322154}`.
After: `{"du_allocated": 112513024, "du_apparent": 111075720, "files": 480, "regular_allocated": 112451584, "regular_apparent": 111075720}`.
Elapsed 3.743 s; aggregate 9.998 s; exit 0; timeout False.

```text
✔ [6/6] Built YulangClosure.SimpleSubRegularConstraintSoundness (3.6s)
Build completed successfully (6 jobs).

```

Created files (SHA-256):

* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubRegularConstraintSoundness.c` — `82855b5faf160eefc065c56264e82f0a6f0917cc37dbbe977fffe09e8ec5eba2`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubRegularConstraintSoundness.c.hash` — `7711a0dbb86d45fb9cbe99a6c779e396f9484d5f02122f6c9ef70984e4ae55f7`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubRegularConstraintSoundness.setup.json` — `3f4efa83f372e7492d116dea93d6b7072a69dc7e0ee56d7ced858c42094751ea`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubRegularConstraintSoundness.ilean` — `b30c1a4619d8b5e99411bad60ba134ac0bceabc3b1ff50974cad0cd0c0cd04a8`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubRegularConstraintSoundness.ilean.hash` — `c5a54898510101f496143c61c2d802250c981b8872be01a0f35b51fe5e54b939`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubRegularConstraintSoundness.olean` — `672256b6522ccbf92433e7a55bb309694b71d5bc9629dca1fdcf599bd0aeb55c`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubRegularConstraintSoundness.olean.hash` — `650beddcb3d182f45ce02a4060c9b33b3a718ef3bcd9a8a9a85c0688ab1c4aa1`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubRegularConstraintSoundness.trace` — `e41e26c1d40c7fbb2516af85cd4ebf9224cd23c4ce91de4b32df910c3fb4e50e`

Modified/deleted existing files: `[]`.
Unexpected created paths: `[]`.

### SimpleSubLatticeCertificates

Command (cwd `notes/theory/lean`):

```sh
env LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR= /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache --fail-fast build +YulangClosure.SimpleSubLatticeCertificates:olean
```

Before: `{"du_allocated": 112513024, "du_apparent": 111075720, "files": 480, "regular_allocated": 112451584, "regular_apparent": 111075720}`.
After: `{"du_allocated": 115167232, "du_apparent": 113707164, "files": 488, "regular_allocated": 115105792, "regular_apparent": 113707164}`.
Elapsed 1.844 s; aggregate 11.842 s; exit 0; timeout False.

```text
✔ [7/7] Built YulangClosure.SimpleSubLatticeCertificates (1.7s)
Build completed successfully (7 jobs).

```

Created files (SHA-256):

* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubLatticeCertificates.c` — `51e475f3a2af9a229ce03be0572ca9c3be3b6929a54a8812ad27b1dab338879f`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubLatticeCertificates.c.hash` — `e619d6ef3d57d4ee7f31f260c8a39c5f3e601a4dc885a213def641c3721b301a`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubLatticeCertificates.setup.json` — `66cb29181a61511fb006e1f148bf4511b9626637dc6d66f3d06fd37bb02ef5f8`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeCertificates.ilean` — `74892e62b7ccebc68f1453561d44b0aa36f3c157be9c2b74cbc15403329501d5`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeCertificates.ilean.hash` — `ebf52f730cbf51be10a56406d5de3eeaa391ba13c68c0421792629296d98eeb5`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeCertificates.olean` — `97dc81b6a99d64f980385535e9434e1b989272b8d786399bee34de4f4b29b931`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeCertificates.olean.hash` — `86d3e2565f37797cb0ea00de1c3c598b6bc80f749cb36712a582cce39847552f`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeCertificates.trace` — `8856abb688b43fae1d596a78f722fa8200424516fc5ac6bc0e59bd3d3685475e`

Modified/deleted existing files: `[]`.
Unexpected created paths: `[]`.

### SimpleSubGeneralizationSoundness

Command (cwd `notes/theory/lean`):

```sh
env LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR= /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache --fail-fast build +YulangClosure.SimpleSubGeneralizationSoundness:olean
```

Before: `{"du_allocated": 115167232, "du_apparent": 113707164, "files": 488, "regular_allocated": 115105792, "regular_apparent": 113707164}`.
After: `{"du_allocated": 115957760, "du_apparent": 114472670, "files": 496, "regular_allocated": 115896320, "regular_apparent": 114472670}`.
Elapsed 0.941 s; aggregate 12.783 s; exit 0; timeout False.

```text
✔ [4/4] Built YulangClosure.SimpleSubGeneralizationSoundness (837ms)
Build completed successfully (4 jobs).

```

Created files (SHA-256):

* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubGeneralizationSoundness.c` — `4305c780e82313a49ca9790ed9d88cba2cfd2eb94dadad4f21ca66577ba801da`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubGeneralizationSoundness.c.hash` — `8f8913ef86ce2cdb47480b5b3f311a9d066682f6a48ab1d0ff4e24b40a47ce2f`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubGeneralizationSoundness.setup.json` — `de79004d003237244b4c5cd2f165c8ca66aabb7d7824b1f049717f4109f2f64d`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubGeneralizationSoundness.ilean` — `1810403b01fb73225543969334b0b806df6489917422fd44aec3637b42d13c83`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubGeneralizationSoundness.ilean.hash` — `1d59ee43b4cfb7e0a0598ddae925a8069fe57c7837cc1226739dddeaad9a1596`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubGeneralizationSoundness.olean` — `cac8c069722ec196699bb9e88119c179c33a53d35ea6f7a27cb0aa619a2b27d4`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubGeneralizationSoundness.olean.hash` — `539ca4fbdaefa13bb924dea4c9bc9bcd74a6d6e82354ff6d579f0471fa67ab52`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubGeneralizationSoundness.trace` — `53a348d76692adda7083d1ddd2acf197b93a0801ea829cb024f13b206007137f`

Modified/deleted existing files: `[]`.
Unexpected created paths: `[]`.

### SimpleSubScopedPublication

Command (cwd `notes/theory/lean`):

```sh
env LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR= /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache --fail-fast build +YulangClosure.SimpleSubScopedPublication:olean
```

Before: `{"du_allocated": 115957760, "du_apparent": 114472670, "files": 496, "regular_allocated": 115896320, "regular_apparent": 114472670}`.
After: `{"du_allocated": 116944896, "du_apparent": 115433179, "files": 504, "regular_allocated": 116883456, "regular_apparent": 115433179}`.
Elapsed 1.244 s; aggregate 14.027 s; exit 0; timeout False.

```text
✔ [5/5] Built YulangClosure.SimpleSubScopedPublication (1.2s)
Build completed successfully (5 jobs).

```

Created files (SHA-256):

* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubScopedPublication.c` — `1aa2c7b1b45234f3ae71f343ed3342657893e4d9aebd0e5f92d49ed1e231b505`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubScopedPublication.c.hash` — `288568df6c1b07878f6a97d51a7a641a6fcf89e28115d0d01ca29feeb90be9ea`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubScopedPublication.setup.json` — `fcbfd2c1fe1b8393096ec776eef23c83228922c49e98b10b5c493d9408805d1f`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubScopedPublication.ilean` — `cd9fefa31f12268ee2968855461cde0bdc110c80f255ddb56edeb63eb5e14f1e`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubScopedPublication.ilean.hash` — `a0a90e521541ac8a459f70adb9c1aafc4e4f63f7957113768e17840569cc6343`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubScopedPublication.olean` — `4228a0674e29c54b1dad8ce4dfb76a70dc6a4b524c2718484bb97f3d5f435e52`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubScopedPublication.olean.hash` — `408365b3e6795914abe46eb2f74790872e0444f18f08ef8ea02c75e51aaff957`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubScopedPublication.trace` — `a74be24db44e5d6f57b423ff77aece15c9d214d4c843a01f617e6515c170f20f`

Modified/deleted existing files: `[]`.
Unexpected created paths: `[]`.

### SimpleSubRegularPublication

Command (cwd `notes/theory/lean`):

```sh
env LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR= /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache --fail-fast build +YulangClosure.SimpleSubRegularPublication:olean
```

Before: `{"du_allocated": 116944896, "du_apparent": 115433179, "files": 504, "regular_allocated": 116883456, "regular_apparent": 115433179}`.
After: `{"du_allocated": 118812672, "du_apparent": 117277154, "files": 512, "regular_allocated": 118751232, "regular_apparent": 117277154}`.
Elapsed 1.944 s; aggregate 15.970 s; exit 0; timeout False.

```text
✔ [9/9] Built YulangClosure.SimpleSubRegularPublication (1.9s)
Build completed successfully (9 jobs).

```

Created files (SHA-256):

* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubRegularPublication.c` — `324a9e9ebfded5a2e69947d86f2beee7addee7de11759c7228e8b4a2a131820f`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubRegularPublication.c.hash` — `eb20911cdeb355b9a296a0aae32cacf9ce27aa2b537d5027bea2a5ba9bf59b5a`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubRegularPublication.setup.json` — `dc3234dc363dd758ffca2188d8ba92f221c6e983ab526b73b0bcfec3a84f57dd`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubRegularPublication.ilean` — `52c6a6f7a61fa32cce53a424707fb004e3c0607babc768e9dfd8dc7f069bc803`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubRegularPublication.ilean.hash` — `480164fb6a756b8f6da140098bc9b621acb84f63c475788ad06e790312d516f0`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubRegularPublication.olean` — `95267c8eced4da1b7afef5b633961ed1a7960d6c4c22c2e4c404629542151dbe`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubRegularPublication.olean.hash` — `d81e4f3303d18b8d51350ea255ce80b9131c4d9376692028f75a5b989e3280ec`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubRegularPublication.trace` — `5209a4c20ac69c64ccd17bba40bceda18940f651ea7ae85e3499cf0294c5bd71`

Modified/deleted existing files: `[]`.
Unexpected created paths: `[]`.

### SimpleSubLatticeInference

Command (cwd `notes/theory/lean`):

```sh
env LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR= /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache --fail-fast build +YulangClosure.SimpleSubLatticeInference:olean
```

Before: `{"du_allocated": 118812672, "du_apparent": 117277154, "files": 512, "regular_allocated": 118751232, "regular_apparent": 117277154}`.
After: `{"du_allocated": 123441152, "du_apparent": 121883126, "files": 520, "regular_allocated": 123379712, "regular_apparent": 121883126}`.
Elapsed 4.745 s; aggregate 20.715 s; exit 0; timeout False.

```text
✔ [11/11] Built YulangClosure.SimpleSubLatticeInference (4.6s)
Build completed successfully (11 jobs).

```

Created files (SHA-256):

* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubLatticeInference.c` — `637c88d205a0baa5b80c78d365557c683ff49d755d3b1965a7efb0fc0e05c364`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubLatticeInference.c.hash` — `e23c463be66507c0c82cdc76155b33324ee064fea1f52440771c361fc12cac7e`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubLatticeInference.setup.json` — `54d589feb59cc8b0140af3b822a22a91bfa65b84eea644acf4a630623a62cb34`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeInference.ilean` — `d9b50da256699fceb00703a7a8bbce5a35e4045aa99b1d379db5ca61d58df590`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeInference.ilean.hash` — `fbe6c93063fd7900f3af96617337f1ee3f0e7ba15076a721a7fec287fa005176`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeInference.olean` — `ea964006de2245376f464ea2378702ed9f1da0d4464cb434ea5855a6c4428a21`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeInference.olean.hash` — `09db37d3e4804e42661c9df8b218a819968bb350569848c1e44e0391c89f7bdb`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeInference.trace` — `d498b939ff45ca83816b8ea288d803d29c6f727fd2cedcb37444cf8c6cc2e1f0`

Modified/deleted existing files: `[]`.
Unexpected created paths: `[]`.

### SimpleSubLatticeDecision

Command (cwd `notes/theory/lean`):

```sh
env LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR= /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache --fail-fast build +YulangClosure.SimpleSubLatticeDecision:olean
```

Before: `{"du_allocated": 123441152, "du_apparent": 121883126, "files": 520, "regular_allocated": 123379712, "regular_apparent": 121883126}`.
After: `{"du_allocated": 125014016, "du_apparent": 123431080, "files": 528, "regular_allocated": 124952576, "regular_apparent": 123431080}`.
Elapsed 2.450 s; aggregate 23.165 s; exit 0; timeout False.

```text
✔ [8/8] Built YulangClosure.SimpleSubLatticeDecision (2.3s)
Build completed successfully (8 jobs).

```

Created files (SHA-256):

* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubLatticeDecision.c` — `cef7046514d31f0f322d5589b7343784ed0df0ee0e51e99f21bb40c22e3b9124`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubLatticeDecision.c.hash` — `68051096ad6ecba1e0aa7e33e00093c3afa7f54e4de25a483a644b5164a432f4`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubLatticeDecision.setup.json` — `4778fb1542ada7bff11a288ae4decae890f6596396cd15136c3bb9138739c70a`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeDecision.ilean` — `dc4eea50784ada9ac528bf893e4c582518c74c278022a1854e3e684f903ecca7`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeDecision.ilean.hash` — `155a04b7a6ef14e7a5a99d4da75d3c6d50ae818a237da190deb448d4cf8c4287`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeDecision.olean` — `b74a4dbea3d7dc3c8bef0cabbc3f785eb6270bcb6489bfccc50403dce66ae7d0`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeDecision.olean.hash` — `1151ab9ca83da6c3ea31b120ffad6f5eaeffb9b46b514d1d1421d6cbce5d324e`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeDecision.trace` — `fa00f6e716c5e323c8b63152e665d8ef68b325b5c9d195ad7c79841d8980b717`

Modified/deleted existing files: `[]`.
Unexpected created paths: `[]`.

### SimpleSubLatticeGrowingInference

Command (cwd `notes/theory/lean`):

```sh
env LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR= /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache --fail-fast build +YulangClosure.SimpleSubLatticeGrowingInference:olean
```

Before: `{"du_allocated": 125014016, "du_apparent": 123431080, "files": 528, "regular_allocated": 124952576, "regular_apparent": 123431080}`.
After: `{"du_allocated": 125648896, "du_apparent": 124044649, "files": 536, "regular_allocated": 125587456, "regular_apparent": 124044649}`.
Elapsed 0.644 s; aggregate 23.809 s; exit 0; timeout False.

```text
✔ [13/13] Built YulangClosure.SimpleSubLatticeGrowingInference (519ms)
Build completed successfully (13 jobs).

```

Created files (SHA-256):

* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubLatticeGrowingInference.c` — `a2f6d99ffb2626d72eaa370d3fb5a993a572938a87c2ab397120266e0ea26b0c`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubLatticeGrowingInference.c.hash` — `e2e7c406bea3d2d3c3c4c5d244b6b2f94ea9528aa7be926d54dedd2881894704`
* `notes/theory/lean/.lake/build/ir/YulangClosure/SimpleSubLatticeGrowingInference.setup.json` — `b0d5007378bb414884e9444ac7467bc934dbda7a502694f63955a9eccf644b5b`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeGrowingInference.ilean` — `cbf4f7881640c14a3b0f60470a3e17941a1373ae2d790059c3ee089b194efbc8`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeGrowingInference.ilean.hash` — `911ea413169a7bb97db8286d653fa4219ef988fb0ea4ed29329ddbb05ecf2360`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeGrowingInference.olean` — `a2f90504676c91c94e6691b6336f33503e171ea9aa01d7300b4a0376d08202aa`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeGrowingInference.olean.hash` — `71ac86a037ee73f7d01a968d1e1432ea507e284d4c769e34faf463811571d9c1`
* `notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeGrowingInference.trace` — `8d4597343ea4309b9930a6e0e46f0936dada4663c885e54a3760ba4edd73fb59`

Modified/deleted existing files: `[]`.
Unexpected created paths: `[]`.

Cache build phase completed. Aggregate measured subprocess wall time 23.809 s.

## Direct Lean construction checks

The helper is not used: it creates unleased /tmp/yulang-lean-audit-* scratch and builds an unqualified module target. Primary explicitly authorized inline queries and direct pinned Lean on the exact leased module.

Check D1: exact pinned `lake --no-cache env lean -j1 -M1024 YulangClosure/AbstractSimpleSubCore.lean`, cwd project, exit 0, before coalescer additions. No diagnostic output.

Check D2: same command after coalescer additions, exit 1 (0.687 s reported wall time). Material diagnostics:

```text
AbstractSimpleSubCore.lean:252:14: error: Type mismatch: Alternative has type List (Term kind), but expected an unresolved match motive.
AbstractSimpleSubCore.lean:254:23: error(lean.invalidField): type of bounds is not known; cannot resolve foldlM.
AbstractSimpleSubCore.lean:280:0: warning: unused termination_by, function is not recursive.
```

The bounds match requires an explicit dependent element type; next repair annotates it. The warning occurs in the failed elaboration and is not evidence that recursive calls have been accepted. No theorem accepted by D2.

### Direct check D9 (final candidate with finite diagnostics)

```sh
env LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR= /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean -j1 -M1024 YulangClosure/AbstractSimpleSubCore.lean
```

Exit 0; measured subprocess wall 6.095 seconds; child peak RSS 545272 KiB; one CPU affinity; timeout 120 s.

```text
YulangClosure.SimpleSub.AbstractCore.CoreProblem.initial : YulangClosure.SimpleSub.AbstractCore.CoreProblem →
  YulangClosure.SimpleSub.AbstractCore.CoreState
YulangClosure.SimpleSub.AbstractCore.CoreState.insertPendingUpper : YulangClosure.SimpleSub.AbstractCore.CoreState →
  Option YulangClosure.SimpleSub.AbstractCore.CoreState
YulangClosure.SimpleSub.AbstractCore.coreCoalesce : YulangClosure.SimpleSub.AbstractCore.CoreCoalescingMode →
  YulangClosure.SimpleSub.AbstractCore.CoreState →
    Nat →
      YulangClosure.SimpleSub.Polarity →
        List YulangClosure.SimpleSub.AbstractCore.CorePolarRow →
          {kind : YulangClosure.SimpleSub.Kind} →
            YulangClosure.SimpleSub.Term kind → Option (YulangClosure.SimpleSub.AbstractCore.CoreCoalesced kind)
YulangClosure.SimpleSub.AbstractCore.CoreState.coalesce : YulangClosure.SimpleSub.AbstractCore.CoreCoalescingMode →
  YulangClosure.SimpleSub.AbstractCore.CoreState →
    YulangClosure.SimpleSub.Polarity →
      {kind : YulangClosure.SimpleSub.Kind} →
        YulangClosure.SimpleSub.Term kind → Option (YulangClosure.SimpleSub.AbstractCore.CoreCoalesced kind)
YulangClosure.SimpleSub.AbstractCore.upper_only_polar_equations : YulangClosure.SimpleSub.AbstractCore.upperOnlyProjection
      YulangClosure.SimpleSub.AbstractCore.CoreCoalescingMode.ordinary YulangClosure.SimpleSub.Polarity.positive =
    some (YulangClosure.SimpleSub.Term.var 0) ∧
  YulangClosure.SimpleSub.AbstractCore.upperOnlyProjection
        YulangClosure.SimpleSub.AbstractCore.CoreCoalescingMode.ordinary YulangClosure.SimpleSub.Polarity.negative =
      some ((YulangClosure.SimpleSub.Term.var 0).intersection (YulangClosure.SimpleSub.Term.atom 0)) ∧
    YulangClosure.SimpleSub.AbstractCore.upperOnlyProjection
          YulangClosure.SimpleSub.AbstractCore.CoreCoalescingMode.unifying YulangClosure.SimpleSub.Polarity.positive =
        some (YulangClosure.SimpleSub.Term.top.intersection (YulangClosure.SimpleSub.Term.atom 0)) ∧
      YulangClosure.SimpleSub.AbstractCore.upperOnlyProjection
          YulangClosure.SimpleSub.AbstractCore.CoreCoalescingMode.unifying YulangClosure.SimpleSub.Polarity.negative =
        some (YulangClosure.SimpleSub.Term.top.intersection (YulangClosure.SimpleSub.Term.atom 0))
'YulangClosure.SimpleSub.AbstractCore.upper_only_polar_equations' depends on axioms: [propext, Quot.sound]
YulangClosure.SimpleSub.AbstractCore.upper_only_shared_satisfies : YulangClosure.SimpleSub.Store.Satisfied
  YulangClosure.SimpleSub.AbstractCore.upperOnlyValuation
  YulangClosure.SimpleSub.AbstractCore.upperOnlyProblem.originalConstraints
'YulangClosure.SimpleSub.AbstractCore.upper_only_shared_satisfies' depends on axioms: [propext]
YulangClosure.SimpleSub.AbstractCore.all_constructors_acyclic_projection : (YulangClosure.SimpleSub.AbstractCore.CoreState.coalesce
          YulangClosure.SimpleSub.AbstractCore.CoreCoalescingMode.ordinary
          YulangClosure.SimpleSub.AbstractCore.emptyProblem.initial YulangClosure.SimpleSub.Polarity.positive
          YulangClosure.SimpleSub.AbstractCore.allConstructorsTerm).bind
      YulangClosure.SimpleSub.AbstractCore.CoreCoalesced.toTerm =
    some YulangClosure.SimpleSub.AbstractCore.allConstructorsTerm ∧
  (YulangClosure.SimpleSub.AbstractCore.CoreState.coalesce
          YulangClosure.SimpleSub.AbstractCore.CoreCoalescingMode.unifying
          YulangClosure.SimpleSub.AbstractCore.emptyProblem.initial YulangClosure.SimpleSub.Polarity.negative
          YulangClosure.SimpleSub.AbstractCore.allConstructorsTerm).bind
      YulangClosure.SimpleSub.AbstractCore.CoreCoalesced.toTerm =
    some YulangClosure.SimpleSub.AbstractCore.allConstructorsTerm
'YulangClosure.SimpleSub.AbstractCore.all_constructors_acyclic_projection' depends on axioms: [propext, Quot.sound]
YulangClosure.SimpleSub.AbstractCore.four_port_variance : YulangClosure.SimpleSub.AbstractCore.portProjection
      YulangClosure.SimpleSub.Polarity.positive =
    some
      (((YulangClosure.SimpleSub.Term.var 0).intersection (YulangClosure.SimpleSub.Term.atom 0)).function
        ((YulangClosure.SimpleSub.Term.var 0).intersection (YulangClosure.SimpleSub.Term.atom 1))
        (YulangClosure.SimpleSub.Term.var 0) (YulangClosure.SimpleSub.Term.var 0)) ∧
  YulangClosure.SimpleSub.AbstractCore.portProjection YulangClosure.SimpleSub.Polarity.negative =
    some
      ((YulangClosure.SimpleSub.Term.var 0).function (YulangClosure.SimpleSub.Term.var 0)
        ((YulangClosure.SimpleSub.Term.var 0).intersection (YulangClosure.SimpleSub.Term.atom 1))
        ((YulangClosure.SimpleSub.Term.var 0).intersection (YulangClosure.SimpleSub.Term.atom 0)))
'YulangClosure.SimpleSub.AbstractCore.four_port_variance' depends on axioms: [propext, Classical.choice, Quot.sound]
YulangClosure.SimpleSub.AbstractCore.ordinary_readout_not_uniform : ¬YulangClosure.SimpleSub.Lattice.RegularSub
    YulangClosure.SimpleSub.AbstractCore.ordinaryFreeGraph
    { kind := YulangClosure.SimpleSub.Kind.value, lower := 1, upper := 2 }
'YulangClosure.SimpleSub.AbstractCore.ordinary_readout_not_uniform' depends on axioms: [propext, Quot.sound]

```

## Frozen result and exact first remaining construction

**STOPPED_INCOMPLETE, Stage A unmet. Stage B was not entered.** No `step`,
`CoreRun`, `CoreAccepted`, `CoreReadout` or whole-run theorem has been defined.
The initialized storage, partial upper-bound operation and finite diagnostic
lemmas are not a concrete whole Simple-sub solver. No supplied history,
`LawfulStore`, arbitrary type-graph solution, terminal certificate, stronger
parent hypothesis, or narrower source language was used to claim completion.

First missing COMPUTATION has the exact source/target types already available:

```lean
-- Required signature only; NOT a delivered declaration or assumed law:
buildSharedReadout : CoreState →
  Option (Lattice.Graph × LatticeInference.References)
-- Lattice.Graph = (kind : SimpleSub.Kind) → List (Lattice.Node kind)
-- LatticeInference.References = SimpleSub.Kind → Nat → Nat
```

It must compute the one graph and reference assignment from the actual bounds,
equality representatives and generated polar outputs. The missing bridge must
then establish `LatticeInference.StoreSatisfied graph refs originalConstraints`
for an actual accepted reachable state; it may not assume that relation.
A compiler of recursive outputs would need a concrete binder environment, e.g.

```lean
compileCoalesced : Lattice.Graph → List (CorePolarRow × Nat) →
  {kind : SimpleSub.Kind} → CoreCoalesced kind → Option (Lattice.Graph × Nat)
```

This signature is an unresolved construction, not permission to supply its
input graph/reference data from outside the core. The initial graph and free
row map must be built by `buildSharedReadout`. Real bound-only cycles and
mixed lattice recursion require a guard-preserving construction/normalization;
the acyclic `CoreCoalesced.toTerm` deliberately returns `none` on bound
occurrences. There is no proof of fuel sufficiency or a general common regular
interpretation of both polar outputs. This blocks first, already before
publication: no complete readout/acceptance can be fixed from the current data.

Second missing generalization computation has concrete intended signatures:

```lean
-- Required signatures only; NOT delivered declarations or theorem premises:
performUse : CoreState → CorePublication → CoreUseRequest → Option CoreState
resolveOriginalUse : CoreState → Nat → ScopedPublication.Row →
  Option ScopedPublication.Row
```

For every performed use and eligible original template coordinate, its required
identity equation is

```text
performUse before publication request = some after
resolveOriginalUse after request.identity template = some actualFreshRow
```

where `actualFreshRow` is the coordinate actually allocated by that operation,
not an independently chosen witness. One per-use memo/map must copy both bound
sides coherently; independent uses have disjoint fresh coordinates while
captured/fixed/non-generic coordinates remain shared under the selected guards.
The current flat `CoreProblem.demands` does not yet translate original
use-coordinate identities to those dynamically allocated coordinates.
`CoreUse` can represent two copy maps with one publication origin, but no actual
publication/use operation creates those maps. Preallocating two input rows or
writing the maps by hand would not establish the required behavior.
**No generalized Int/Bool accepted-run test or theorem is claimed.**

The precise Int/Bool falsifier for the next owner remains: two independent
uses of one generalized identity must allocate distinct instance rows and
admit Int and Bool clients independently, while retaining one publication
origin and all prescribed shared captures. The existing metadata transport
and published-clause-image lemmas require closure/allocation facts; they do
not establish these operations or this coordinate identity equation.

## Meaning and limits of the checked finite results

All five delivered theorems are in `YulangClosure.SimpleSub.AbstractCore`.
Their exact printed types and COMPLETE axiom lists are in D9 above:

| Theorem | Complete axioms |
| --- | --- |
| `upper_only_polar_equations` | `propext`, `Quot.sound` |
| `upper_only_shared_satisfies` | `propext` |
| `all_constructors_acyclic_projection` | `propext`, `Quot.sound` |
| `four_port_variance` | `propext`, `Classical.choice`, `Quot.sound` |
| `ordinary_readout_not_uniform` | `propext`, `Quot.sound` |

The upper-only state is computed from `CoreProblem.initial` and one actual
upper-bound insertion with opposite-bound replay. For `x <: Int`, ordinary
positive/negative outputs project to `x` and `x & Int`; the Fig.12 unifying
outputs project to the same `Top & Int`, whose one explicit valuation satisfies
that finite original store. This is an acyclic example, not the general bridge.

`ordinary_readout_not_uniform` is a finite counterinterpretation to the
shortcut that treats the ordinary free name as an arbitrary shared solution:
choose Bool for the free name, and the independent regular relation rejects
`Bool <: Bool & Int`. It is **not a counterexample to R211**; there is a common
Int-bearing interpretation, as the preceding finite theorem shows. The exact
missing hypothesis for arbitrary ordinary free substitutions would be that
they satisfy the row's upper bounds; adding that as a parent assumption would
move the requested conclusion into a premise. The intended repair is the
constructed unifying/shared readout and derived whole-run invariants.

The constructor example exercises both kinds, atoms, bottom/top,
union/intersection, all Function ports, records including label and optional
bit, tuple order, variant tag and payload spine. `four_port_variance` uses
actual Value and Effect upper bounds to distinguish both contravariant ports
from both covariant ports in each input polarity. The source declarations
cover recursive row memo identity in both polarities, but no all-cycle graph
compiler/semantic theorem, level-aware copying transition, SCC activation,
equality merge, full lower-bound operation, publication/use transition or
finite run was completed. No accepted input cases were narrowed to promote a
whole-language result; the entire R211 gate remains open.

## Failed checks and repairs (preserved evidence)

There were **nine direct file checks D1–D9**, and **zero `check_lean.py`
invocations**. The initial packet caps helper invocations; primary explicitly
authorized direct exact-module checking because helper scratch is outside the
lease. No helper target, default Lake target, audit scratch or new environment
was created. D1 checked initial storage before coalescing; D4 checked coalescer
definitions; D8 and D9 checked the finite lemmas. D1/D4/D8/D9 exited 0.
D2/D3/D5/D6/D7 exited 1; none is a proof receipt.

D2's actual dependent bounds-type failure is preserved above. D3 then reported:
`incomplete set of termination hints: ... mutually recursive with ...
coreCoalesce.visit, which does not have a termination hint.` Repair: outer
measure `(fuel,0)` and local-visit measure `(fuel,sizeOf subterm+1)`. Structural
traversal preserves fuel; entering another row decreases it, with seen
(kind,row,polarity) keys retaining cycles. D4 exited 0 and printed types.

D5 failed `rfl` for the unifying-negative projection and the unifying-negative
all-constructor projection. D6 added `#reduce` to inspect the computation;
reduction expanded the well-founded `Acc.rec` encoding rather than providing
a short normal form. Its captured output was truncated (11,963 tokens), and
it is not claimed as a computed model. The two failed declarations printed
`sorryAx` due to Lean's error recovery. No `sorry`/`admit` was authored, and no
failed declaration was delivered as proved. The diagnostic reduction commands
were removed.

D7 replaced reflexivity with rewriting by the function equations. The
all-constructor theorem passed, but the upper-only equation left a concrete
unsolved goal containing `ScopedPublication.vars (Term.atom 0)` and
`CoreRow.initial` projections; failed-theorem axioms still included `sorryAx`.
Repair: unfold those two actual definitions in the finite calculation. D8
exited 0 with no `sorryAx`. D9 added and checked four-port variance and the
ordinary free-name counterinterpretation. Its full successful output, measured
wall time and RSS are preserved above. D1–D8 total wall/CPU/RSS were not
instrumented; no numerical aggregate for those checks is fabricated.

## Original source, parent application and authority

The R211 frozen handoff linked above contains the original manuscript and
source-preservation claim, current birth-level correction, exact root
quantifiers and original source/Call/effect/shared-witness boundary. This
packet reused those actual sources and the pinned definitions; it did not
adopt research drafts as semantics. Coalescing follows paper Figs.11–12,
including distinct ordinary/unifying modes; the paper's non-let proof scope
is not silently extended to publication or Yulang source soundness.

The original fully qualified roots are `YulangClosure.SourceProblem`'s
`InferenceSoundness`, `PrincipalCoverage`, `InferenceTermination` and
`SourceScopedCoverage`. The new finite results do not establish a concrete
source instance, generation/solving adequacy, `sameScoped` readout, source
coverage, principality/order, termination, or source/native correspondence.
There is no reviewed application to an unchanged original parent premise.
**Accounting remains 0/4 roots; 0/5 packages.** No production promotion or
independent review is claimed. Primary owns the next readout/allocation packet,
fresh independent review and integration; the writer cannot self-certify.

## Freeze hashes, sizes, scope and cessation

Module SHA-256: `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c`.

Final `.lake` sizes: `{"du_allocated": 125648896, "du_apparent": 124044649, "files": 536, "regular_allocated": 125587456, "regular_apparent": 124044649}`. Incremental apparent growth is 22,211,438 bytes; incremental regular allocated growth is 22,474,752 bytes. All 88 created artifact hashes still match their per-build receipts; all source/tool/authority pins still match. The final direct checks created no additional `.lake` regular files.

R212 source pins (under `notes/theory/lean/YulangClosure/`):

```text
2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e Contracts.lean
a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6 SimpleSubConstraintSyntax.lean
33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293 SimpleSubConstraintSoundness.lean
755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29 SimpleSubRegularSolutions.lean
1d2266867115fc27afe39dbb80a3ca0e8f75247a2e16b739145137e83999de33 SimpleSubRegularConstraintSoundness.lean
55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b SimpleSubLatticeCertificates.lean
3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246 SimpleSubGeneralizationSoundness.lean
d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f SimpleSubScopedPublication.lean
18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99 SimpleSubRegularPublication.lean
c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3 SimpleSubLatticeInference.lean
a9c184512bf6e23d15cc8a3a2ed230652fb168f707155e779be18c562d8e57c9 SimpleSubLatticeDecision.lean
1270e3407ddeef881020610b094709ebba07b62a97e54712bcc4b139ef8e78d0 SimpleSubLatticeGrowingInference.lean
```

R212 tool pins:

```text
ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c lean-toolchain
212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4 lakefile.toml
058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3 lake-manifest.json
```

All unchanged R211 pins rechecked at freeze:

```text
2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e notes/theory/lean/YulangClosure/Contracts.lean
a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6 notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean
33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293 notes/theory/lean/YulangClosure/SimpleSubConstraintSoundness.lean
c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3 notes/theory/lean/YulangClosure/SimpleSubLatticeInference.lean
1270e3407ddeef881020610b094709ebba07b62a97e54712bcc4b139ef8e78d0 notes/theory/lean/YulangClosure/SimpleSubLatticeGrowingInference.lean
865b9eb4a64962182a22a9e507b98b1e7ab92ac143e4cbfea0b8570e39bb58ce notes/theory/lean/YulangClosure/SimpleSubGrowingInference.lean
d7231d0a3695dba7f3102e5fe235d4d26e34cad78870dbdbae9b7633c42787aa notes/theory/lean/YulangClosure/SimpleSubRegularCompletion.lean
6b6e5e6f1c45140d935e1aa29fba4c1303ae89cd91fd6e1cde0d37387148db8d notes/theory/lean/YulangClosure/SimpleSubRegularDecision.lean
a9c184512bf6e23d15cc8a3a2ed230652fb168f707155e779be18c562d8e57c9 notes/theory/lean/YulangClosure/SimpleSubLatticeDecision.lean
d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f notes/theory/lean/YulangClosure/SimpleSubScopedPublication.lean
3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246 notes/theory/lean/YulangClosure/SimpleSubGeneralizationSoundness.lean
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 notes/design/2026-10-11-yulang-inference-top-level-principles.md
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b notes/design/2026-10-10-parent-copy-scc-intrusion.md
f4d3bd7e89ae26ecba0baeaaa351e82037ff0cf268c815e64b638dbbabfb2493 notes/theory/2026-10-10-simple-sub-complete-bound-accumulation.md
8dd8eb55ac9d9df75980182cb5483f9394674a94f77c9d70d12f89b5be0d24e6 notes/theory/2026-10-11-simple-sub-value-reference-scc.md
```

Dependency-cone hole/bypass scan command: `rg -n \b(sorry|admit|axiom)\b|debug\.skipKernelTC|native_decide` on the new module and all 12 frozen local imports. Actual exit 1; matches:

```text

```

Cache generation:12 sequential OLean commands, all exit0, aggregate23.809s, no timeout/cap crossing, exactly88 whitelisted new outputs, no preexisting outputs modified/deleted by those builds. D9:6.095s and545272KiB child peak RSS, CPU affinity one, timeout120s; project -j1/-M1024 retained. No Rust/tests/Git/config/dependency/toolchain/source-import-root writes, no children, no remote cache, no cleanup. Primary-owned dirty/quarantined files were preserved. No Stage B allowance was used or reset.

Freeze UTC 2026-11-01T19:40:28.002903+00:00. **WRITES STOPPED after this handoff revision.** No subprocess/child/generated-output writer remains. No exact module, handoff or artifact write will resume without a new primary packet. Only the exact cache whitelist, module and this one handoff were written.
