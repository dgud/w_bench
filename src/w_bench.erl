-module(w_bench).
-export([start/0, start/1]).

-include("wings.hrl").

start() ->
    start(6).

start(Levels) ->
    We0 = init_data(),
    We = wings_subdiv:smooth(We0),
    repeat(10, We, Levels, 10, 0).

repeat(N, We, Levels, Tot, Acc) when N > 0 ->
    Parent = self(),
    spawn_opt(fun() ->
                      {Time, #we{}} = timer:tc(fun() -> run(We, Levels) end),
                      Parent ! {time, Time}
              end, [{min_heap_size, 32*1204}]),
    Time = receive {time, T} -> T end,
    repeat(N-1, We, Levels, Tot, Acc+(Time div 1000));
repeat(0, _We, _, N, Acc) ->
    Acc div N.

run(We0, Level) when Level > 0 ->
    We = wings_subdiv:smooth(We0),
    run(We, Level-1);
run(We, 0) ->
    We.

init_data() ->
    Es = [{0,{edge,0,1,5,1,3,1,2,4}},{1,{edge,0,2,3,5,6,2,0,5}},
          {2,{edge,0,4,1,3,8,0,1,9}},{3,{edge,1,3,5,2,5,0,4,7}},
          {4,{edge,1,5,2,1,10,3,0,8}},{5,{edge,2,3,0,5,7,6,1,3}},
          {6,{edge,2,6,3,0,9,1,5,11}},{7,{edge,3,7,0,2,11,5,3,10}},
          {8,{edge,4,5,1,4,4,2,9,10}},{9,{edge,4,6,4,3,11,8,2,6}},
          {10,{edge,5,7,2,4,7,4,8,11}},{11,{edge,6,7,4,0,10,9,6,7}}],
    Fs = [{0,5},{1,0},{2,3},{3,1},{4,8},{5,0}],
    Vc = [{0,0},{1,0},{2,1},{3,3},{4,2},{5,4},{6,6},{7,7}],
    Vp = [{0,{-1.0,-1.0,-1.0}}, {1,{-1.0,-1.0,1.0}}, {2,{-1.0,1.0,-1.0}},
          {3,{-1.0,1.0,1.0}}, {4,{1.0,-1.0,-1.0}}, {5,{1.0,-1.0,1.0}},
          {6,{1.0,1.0,-1.0}}, {7,{1.0,1.0,1.0}}],
    #we{id=1, perm=1, name="TestCube",
        es = array:from_orddict(Es),
        lv = none,rv = none,
        fs = gb_trees:from_orddict(Fs),
        he = gb_sets:empty(),
        vc = array:from_orddict(Vc),
        vp = array:from_orddict(Vp),
        pst = gb_trees:empty(),
        mat = default,next_id = 12,
        mirror = none,light = none,
        holes = [],temp = []
       }.
