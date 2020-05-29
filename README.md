w_bench
=====

A benchmark of wings3d work

Build
-----

    $ rebar3 compile
	$ erl -pa _build/default/lib/w_bench/ebin/ -noshell -s w_bench -s erlang halt
