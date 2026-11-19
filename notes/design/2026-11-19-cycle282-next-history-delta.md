# 次サイクル: prospective 検査を差分化する契約
今回の compile は各 state の全履歴を sort して読む。次は graph/canonical source の既存 reader と合わせ、候補 effect だけを追加した時に、以前の field はどこまで読み直さなくてよいかを source kernel から出す。

1. 旧 entries と新 entries の兼用 target は同じ key なら同じ RHS という実台帳既存結果で落とす。残りの新 target を「旧 compiled journal の typed 支持に現れるもの」と「現れないもの」に分ける。前者を無条件に silent と扱わない。予約 metadata だけの識別子は semantic reads と区別する。
2. 新 target が旧 compiled 支持に現れないとき、旧 compiler の cache を保持して新 effect/live requirements だけを増分検査し、全 replay と同じであることを、履歴拡張の ordered solve の合成則と atom の支持で示す。異なる順序でも全定義の意味が同じという補題を別に立てる。
3. SameInputs / Equal は今回の compiled query へ運べる。次に Generated / Known / Local の operator を fixed graph の読戻しと合わせる。元 journal を読まずに実証する初期断片として、Display 非葉、optional の旧→point 下端の上書き、および 239/240 の二セルを選ぶ。
4. アドレス個数、正規形 RHS の大きさ、証拠 phase の有限性は別物。共通有限チャートには、source/owner 固定型項上の支持閉包またはその反例が必要。無制限 driver の exactness と guarded termination を混同しない。
