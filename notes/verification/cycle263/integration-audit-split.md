# Supervisor cycle257 audit split

- lean/Audit/Cycle257Complete.lean: exact integration bytes, sha256 6b9e2edf809b34ab3c53292b3f077bc1253cf6eb0c36db4a9579843dc61aff4f
- lean/Audit/Cycle257Full.lean: exact integration bytes, sha256 4a2ae84b5659c77b8958c648e66777eacebcb67cc9a6312e3e29329489714c1c
- lean/Audit/Cycle257CompleteExtra.lean: exact integration bytes, sha256 4fce1436a7214739fd01b8f077b3479fdc2d91b1cc741949e8d4c2423d74eb15
- lean/Audit/Cycle257FullExtra.lean: exact integration bytes, sha256 ac617cea498dcc14a3e41137d48c9b70cf3f2b869de01bde60c123e69d8405c6

Copied exact integration files, no cycle263 additions inside frozen audits. Historical audit rerun recorded separately.

All four historical audits passed individually with lake env lean --trust=0 -DwarningAsError=true. See reconciled257-{Complete,Full,CompleteExtra,FullExtra}.txt.
