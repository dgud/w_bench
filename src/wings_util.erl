%%
%%  wings_util.erl --
%%
%%     Various utility functions that not obviously fit somewhere else.
%%
%%  Copyright (c) 2001-2011 Bjorn Gustavsson
%%
%%  See the file "license.terms" for information on usage and redistribution
%%  of this file, and for a DISCLAIMER OF ALL WARRANTIES.
%%
%%     $Id$
%%
%% Note: To keep the call graph clean, wings_util MUST NOT call
%%       other wings_* modules (except wings_pref).

-module(wings_util).
-export([share/1,share/3,make_vector/1,
	 rel2fam/1,
	 format/2,
	 key_format/2,
	 cap/1,upper/1,quote/1,
	 add_vpos/2,update_vpos/2,
	 gb_trees_smallest_key/1,gb_trees_largest_key/1,
	 array_keys/1,array_smallest_key/1,array_greatest_key/1,
	 array_is_empty/1,array_entries/1,
	 mapsfind/3,
	 nice_float/1,nice_vector/1,nice_abs_vector/1,
         string_to_float/1,
	 unique_name/2,
	 is_name_masked/2,
	 lib_dir/1,
	 tc/3, profile_start/1, profile_stop/1,
	 limit/2]).

-include("wings.hrl").
-include_lib("e3d.hrl").

-import(lists, [foldl/3,reverse/1,member/2,last/1]).

share(X, X, X) -> {X,X,X};
share(X, X, Z) -> {X,X,Z};
share(X, Y, Y) -> {X,Y,Y};
share(X, Y, X) -> {X,Y,X};
share(X, Y, Z) -> {X,Y,Z}.

share({X,X,X}) -> {X,X,X};
share({X,X,Z}) -> {X,X,Z};
share({X,Y,Y}) -> {X,Y,Y};
share({X,Y,X}) -> {X,Y,X};
%%
share({X,X,X,X}) -> {X,X,X,X};
%%
share({X,X,X,A}) -> {X,X,X,A};
share({X,X,Z,X}) -> {X,X,Z,X};
share({X,Y,X,X}) -> {X,Y,X,X};
share({X,Y,Y,Y}) -> {X,Y,Y,Y};
%%
share({X,X,Y,Y}) -> {X,X,Y,Y};
share({X,Y,X,Y}) -> {X,Y,X,Y};
share({X,Y,Y,X}) -> {X,Y,Y,X};
%%
share({X,X,Z,A}) -> {X,X,Z,A};
share({X,Y,X,A}) -> {X,Y,X,A};
share({X,Y,Z,X}) -> {X,Y,Z,X};
share({X,Y,Y,A}) -> {X,Y,Y,A};
share({X,Y,Z,Y}) -> {X,Y,Z,Y};
share({X,Y,Z,Z}) -> {X,Y,Z,Z};
%%
share(Other) -> Other.

make_vector({_,_,_}=Vec) -> Vec;
make_vector(x) -> {1.0,0.0,0.0};
make_vector(y) -> {0.0,1.0,0.0};
make_vector(z) -> {0.0,0.0,1.0};
make_vector(free) -> free;
make_vector(normal) -> normal;
make_vector(intrude) -> normal;
make_vector({region,normal}) -> normal;
make_vector(Axis) when Axis == last_axis; Axis == default_axis ->
    {_,Vec} = wings_pref:get_value(Axis),
    Vec.


key_format(Key, Msg) ->
    [Key,160,Msg].

%% Like io_lib:format/2, but with very restricted format characters.
%% BUT allows arguments to ~s to be lists containing Unicode characters.
%% Now allows ~ts for translation of Asian glyphs.
%%
%% Format directives allowed: ~s ~p

format(Format, Args) ->
    format_1(Format, Args, []).

rel2fam(Rel) ->
    sofs:to_external(sofs:relation_to_family(sofs:relation(Rel))).

quote(Str) when is_list(Str) ->
    [$",Str,$"].


cap(Str) when is_atom(Str) -> cap(atom_to_list(Str));
cap(Str) -> cap(Str, true).

cap([Lower|T], true) when $a =< Lower, Lower =< $z ->
    [Lower-$a+$A|cap(T, false)];
cap([$_|T], _Any) ->
    [$\s|cap(T, true)];
cap([H|T], _Any) ->
    [H|cap(T, false)];
cap([], _Flag) -> [].
    
upper(Str) when is_atom(Str) -> upper(atom_to_list(Str));
upper([Lower|T]) when $a =< Lower, Lower =< $z ->
    [Lower-$a+$A|upper(T)];
upper([H|T]) ->
    [H|upper(T)];
upper([]) -> [].

add_vpos(Vs, #we{vp=Vtab}) -> add_vpos(Vs, Vtab);
add_vpos(Vs, Vtab) ->
    foldl(fun(V, A) ->
		  [{V,array:get(V, Vtab)}|A]
	  end, [], Vs).

update_vpos(Vs, #we{vp=Vtab}) -> update_vpos(Vs, Vtab);
update_vpos(Vs, Vtab) ->
    foldl(fun({V,_}, A) ->
		  [{V,array:get(V, Vtab)}|A];
	     ({V,_,Dist,Inf}, A) ->
		  [{V,array:get(V, Vtab),Dist,Inf}|A]
	  end, [], reverse(Vs)).

gb_trees_smallest_key(Tree) ->
    {Key,_Val} = gb_trees:smallest(Tree),
    Key.

gb_trees_largest_key(Tree) ->
    {Key,_Val} = gb_trees:largest(Tree),
    Key.

array_keys(Array) ->
    array:sparse_foldr(fun(I, _, A) -> [I|A] end, [], Array).

array_smallest_key(Array) ->
    try
	array:sparse_foldl(fun(I, _, _) -> throw(I) end, [], Array),
	error(empty_array)
    catch
	throw:I when is_integer(I) ->
	    I
    end.

array_greatest_key(Array) ->
    try
	array:sparse_foldr(fun(I, _, _) -> throw(I) end, [], Array),
	error(empty_array)
    catch
	throw:I when is_integer(I) ->
	    I
    end.

array_is_empty(Array) ->
    try
	array:sparse_foldr(fun(_, _, _) -> throw(false) end, [], Array),
	throw(true)
    catch
	throw:Empty ->
	    Empty
    end.

%% array_entries(Array) -> NumberOfEntries
%%  Return the number of non-default entries in the array.
%%
array_entries(Array) ->
    array:sparse_foldl(fun(_, _, N) -> N + 1 end, 0, Array).

-spec nice_abs_vector(e3d_vec:vector()) -> iolist().

nice_abs_vector({X,Y,Z}) ->
    nice_vector({abs(X),abs(Y),abs(Z)}).

-spec nice_vector(e3d_vec:vector()) -> iolist().

nice_vector({X,Y,Z}) ->
    ["<",
     wings_util:nice_float(X),"  ",
     wings_util:nice_float(Y),"  ",
     wings_util:nice_float(Z),
     ">"].

nice_float(F) when is_float(F) ->
    simplify_float(lists:flatten(io_lib:format("~f", [F]))).

simplify_float(F) ->
    reverse(simplify_float_1(reverse(F))).

simplify_float_1("0."++_=F) -> F;
simplify_float_1("0"++F) -> simplify_float_1(F);
simplify_float_1(F) -> F.


string_to_float(Str) ->
    try list_to_float(Str)
    catch _:_ -> make_float2(Str)
    end.

make_float2(Str) ->
    try float(list_to_integer(Str))
    catch _:_ -> make_float3(Str)
    end.

make_float3(Str0) ->
    Str = lists:flatten(string:tokens(Str0, "\t\s\n")),
    try list_to_float(Str)
    catch _:_ -> make_float4(Str) end.

make_float4(Str) ->
    WithDot = case string:tokens(Str, "eE") of
		  [Pre,Post] -> Pre ++ ".0e" ++ Post;
		  [Other] -> Other ++ ".0";
		  Other -> Other
	      end,
    list_to_float(WithDot).

%%
%% Finds the first map containing Key:=Value
%%
-spec mapsfind(term(), term(), list()) -> map()|false.
mapsfind(Value, Key, [H|T]) ->
    case H of
	#{Key:=Value} -> H;
	_ -> mapsfind(Value, Key, T)
    end;
mapsfind(_, _, []) -> false.


%%
%% Create a unique name by appending digits.
%%

unique_name(Name, Names) ->
    case member(Name, Names) of
	false -> Name;
	true -> unique_name_1(reverse(Name), Names)
    end.

unique_name_1([C|Cs], Names) when $0 =< C, C =< $9, Cs /= [] ->
    unique_name_1(Cs, Names);
unique_name_1(Name, Names0) ->
    Base0 = [First|_] = reverse(Name),
    Names = [N || N <- Names0, hd(N) =:= First],
    Base = case member($\s, Base0) andalso last(Base0) =/= $\s of
	       true -> Base0 ++ " ";
	       false -> Base0
	   end,
    unique_name_2(Base, 2, gb_sets:from_list(Names)).

unique_name_2(Base, I, Names) ->
    Name = Base ++ integer_to_list(I),
    case gb_sets:is_member(Name, Names) of
	true -> unique_name_2(Base, I+1, Names);
	false -> Name
    end.

tc(Fun,Mod,Line) ->
    Before = os:timestamp(),
    R = Fun(),
    After = os:timestamp(),
    io:format("~p:~p: Time: ~p\n", [Mod, Line, timer:now_diff(After,Before)]),
    R.

profile_start(fprof) ->
    fprof:trace(start),
    ok;
profile_start(eprof) ->
    eprof:start(),
    profiling = eprof:start_profiling([whereis(wings), self(), whereis(wings_image)]),
    ok.

profile_stop(fprof) ->
    fprof:trace(stop),
    spawn_link(fun() ->
                       File = "fprof.analysis",
                       fprof:profile(),
                       fprof:analyse([{dest, File}, {cols, 120}]),
                       io:format("Analysis in: ~p~n", [filename:absname(File)]),
                       eprof:stop()
               end),
    ok;
profile_stop(eprof) ->
    eprof:stop_profiling(),
    spawn_link(fun() ->
                       File = "eprof.analysis",
                       eprof:log(File),
                       eprof:analyze(),
                       io:format("Analysis in: ~p~n", [filename:absname(File)])
               end).

limit(Val, {'-infinity',infinity}) -> Val;
limit(Val, {Min,infinity}) when Val < Min -> Min;
limit(Val, {'-infinity',Max}) when Val > Max -> Max;
limit(Val, {Min,Max}) when Min < Max, Val < Min -> Min;
limit(Val, {Min,Max}) when Min < Max, Val > Max -> Max;
limit(Val, {Min,Max}) when Min < Max -> Val.

%%
%% Check if name match with the mask.
%%

is_name_masked(Name,Mask) ->
    Mask0=string:to_upper(Mask),
    Name0=string:to_upper(Name),
    is_name_masked_0(Name0,Mask0,get_mask_pos(Mask0)).

is_name_masked_0(_Name,"*",_MaskPos) -> true;
is_name_masked_0([],_Mask,_MaskPos) -> false;
is_name_masked_0(_Name,[],_MaskPos) -> false;
is_name_masked_0(Name,Name,[]) -> true;
is_name_masked_0(_Name,_Mask,[]) -> false;
is_name_masked_0(Name,Mask,[H|[]]=_MaskPos) ->  % *text with only one wildcard
    Mlen=string:len(Mask),
    case H of
    1 ->     % *text value
        Mask0=string:sub_string(Mask,H+1),
        MPos=string:rstr(Name,Mask0),
        (string:len(Name)-MPos+1)=:=(Mlen-1);
    Mlen ->  % text value*
        Mask0=string:sub_string(Mask,1,Mlen-1),
        string:str(Name,Mask0)=:=1;
    _ ->     % text *value
        Mask0=string:sub_string(Mask,1,H-1),
        Mask1=string:sub_string(Mask,H+1),
        MPos=string:rstr(Name,Mask1),
        Mlen0=string:len(Mask1),
        (string:str(Name,Mask0)=:=1) and ((string:len(Name)-MPos)=:=(Mlen0-1))
    end;
is_name_masked_0(Name,Mask,[H|[H0|_T0]=_T]=_MaskPos) ->  % *text with more than one wildcard
    case H of
    1 ->     % *text value
        Mask0=string:sub_string(Mask,H+1,H0-1),
        Mask1=string:sub_string(Mask,H0),
        case string:str(Name,Mask0) of
        0 -> false;
        NPos ->
            Name0=string:sub_string(Name,NPos+H0-H-1),
            is_name_masked_0(Name0,Mask1,get_mask_pos(Mask1))
        end;
    _ ->     % te*xt value*
        Mask0=string:sub_string(Mask,1,H-1),
        Mask1=string:sub_string(Mask,H),
        case string:str(Name,Mask0) of
        1 ->
            Name0=string:sub_string(Name,H),
            is_name_masked_0(Name0,Mask1,get_mask_pos(Mask1));
        _ -> false
        end
    end.

%%%
%%% Local functions.
%%%

format_1("~s"++F, [S0|Args], Acc) ->
    S = if
	    is_atom(S0) -> atom_to_list(S0);
	    is_list(S0) -> S0;
	    true -> 
		io:format("Bad string formatter for ~p in ~p~n", 
			  [S0, lists:flatten(reverse(Acc) ++ F)]),
		error(badarg)
	end,
    format_1(F, Args, [S|Acc]);
format_1("~p"++F, [S0|Args], Acc) ->
    S = format_p(S0),
    format_1(F, Args, [S|Acc]);
format_1("~~"++F, Args, Acc) ->
    format_1(F, Args, [$~|Acc]);
format_1("~ts"++F, Args, Acc) ->
    format_1("~s"++F, Args, Acc);
format_1([C|F], Args, Acc) when C =/= $~ ->
    format_1(F, Args, [C|Acc]);
format_1([], [], Acc) -> reverse(Acc).

format_p(Str) when is_list(Str)  ->
    [$",Str,$"];
format_p(Str) ->
    io_lib:format("~p", [Str]).

lib_dir(wings) ->
    case code:lib_dir(wings) of
	{error,bad_name} ->
	    ["wings.beam","ebin"|Rev] = lists:reverse(filename:split(code:which(wings))),
	    filename:join(lists:reverse(Rev));
	Dir -> 
	    Dir
    end;
lib_dir(Lib) ->
    code:lib_dir(Lib).

get_mask_pos([]) -> [];
get_mask_pos(Mask) ->
    get_mask_pos_1(Mask,0,[]).

get_mask_pos_1([],_,Acc) -> Acc;
get_mask_pos_1(Mask,Offset,Acc) ->
    case string:str(Mask,"*") of
    0 -> Acc;
    Pos ->
        Pos0=Pos+Offset,
        get_mask_pos_1(string:sub_string(Mask,Pos+1),Pos0,Acc++[Pos0])
    end.

