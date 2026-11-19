# Cycle 282 — raw 支持を越える固定集約ポートの分離
固定 purpose 0/1 position 0 のポートは、観測 raw state だけでなく、履歴 plan、履歴 effect、live class の読み出しとも分離できるか。各候補を、旧 source の構造 ID・versioned 予約・固定目的 2–9 に分ける。分離が証明できる範囲では置き換えポートを独立に実現し、投入前後で全 journal の Models / dictionary Evidence を一つの共有割当に運ぶ。旧 versioned 値を使う consumer を消すのではなく、証拠を含め別に保持する。後から旧 versioned 参照自体を排除するには、時系列の definition 展開を証明する。一般の後継境界との双方向完全性はこの構成から自動ではない。
