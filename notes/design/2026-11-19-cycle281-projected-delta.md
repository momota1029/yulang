# Cycle 281 — 有限 chart の完全性を得るための差分の型

chart の分離力を仮定するだけでは compiler にならない。次の十分条件を存在射影のレベルで使う。次状態の full models が (old model) ∧ (新しい私有ポートの等式) ∧ (有限の公開 delta の意味) と正確に因数分解され、各 delta は固定公開の agreement で不変。私有ポートは old の支持と公開観測から離れ、同時コピーで解ける。そうすれば任意の公開割当について後状態への拡張存在は old の拡張存在 ∧ 全公開 delta と同値。個々の制約の別々の拡張を併用してはいけない。

strictness は「delta のうち old でまだ必然でないものが一つある」と同値。初期公開条件を base として固定すれば、複数 install に渡って delta を連結するだけで、到達 chart の完全性を継承できる。任意の実 packet をこの因数分解へ compile すること、私有ポートの支持の分離を一般 source から出すことは別義務。実 point service の aggregate 修理は私有差分の特例で、名前の有限性だけから一般解を仮定しない。
