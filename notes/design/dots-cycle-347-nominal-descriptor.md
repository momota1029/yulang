# C347 初回検証点

実 `State.nominals` の物理レイアウトを、順序を保つ名前つき区間として読む。type と row のナンバースペースを区別し、両端が異なっていても落とさない。`read_exact` は格納済みの descriptor と厳密に対応し、`observes` は全 raw models に実パラメータの存在と root denotation を保つ。端点を中心に代用しない。これ自体は native where の生成、authored input、候補選定をまだ示さない。
