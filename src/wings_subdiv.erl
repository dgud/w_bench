%%
%%  wings_subdiv.erl --
%%
%%     This module implements the Smooth command for objects and faces.
%%
%%  Copyright (c) 2001-2011 Bjorn Gustavsson
%%
%%  See the file "license.terms" for information on usage and redistribution
%%  of this file, and for a DISCLAIMER OF ALL WARRANTIES.
%%
%%     $Id$
%%

-module(wings_subdiv).
-export([smooth/1]).

-include("wings.hrl").

-import(lists, [reverse/1,reverse/2,sort/1,foldl/3]).

%%% The Catmull-Clark subdivision algorithm is used, with
%%% Tony DeRose's extensions for creases.

%% smooth(We) -> We'
%%  Sub-divide an entire object.
%%
smooth(We) ->
    {Fs,Htab} = smooth_faces_htab(We),
    #we{vp=Vtab,es=Etab} = We,
    Vs = wings_util:array_keys(Vtab),
    Es = wings_util:array_keys(Etab),
    smooth(true, Fs, Vs, Es, Htab, We).

%% smooth(EntireObject, [Face], [Vertex], [Edge], [HardEdge], We) -> We'
%%  Sub-divide only one or more regions of faces. EntireObject
%%  is a boolean.
%%
smooth(EntireObject, Fs, Vs, Es, Htab, #we{vp=Vp,next_id=Id}=We0) ->
    FacePos0 = face_centers(Fs, We0),

    %% First do all topological changes to the edge table.
    We1 = cut_edges(Es, Htab, We0#we{vc=undefined}),
    We2 = smooth_materials(Fs, FacePos0, We1),
    {We3,Hide} = smooth_faces(FacePos0, Id, We2),

    %% Now calculate all vertex positions.
    FacePos = gb_trees:from_orddict([{F,Pos} || {F,{Pos,_,_}} <- FacePos0]),
    {RevUpdatedVs,Mid} =
	case EntireObject of
	    true ->
		update_edge_vs_all(We0, FacePos, Htab, Vp, Id);
	    false ->
		update_edge_vs_some(Es, We0, FacePos, Htab, Vp, Id)
	end,
    VtabTail = smooth_new_vs(FacePos0, Mid, RevUpdatedVs),
    Vtab = smooth_move_orig(EntireObject, Vs, FacePos, Htab, We0, VtabTail),

    %% Done, except that we'll need to re-hide any hidden faces
    %% and rebuild tables.
    We4 = We3#we{vp=Vtab},
    We = if
	     Hide =:= [] ->
		 wings_we:rebuild(We4);
	     true ->
		 wings_we:hide_faces(Hide, We4) %Will force a rebuild.
	 end,
    We.


smooth_faces_htab(#we{mirror=none,fs=Ftab,he=Htab,holes=[]}) ->
    Faces = gb_trees:keys(Ftab),
    {Faces,Htab};
smooth_faces_htab(#we{mirror=Mirror,fs=Ftab,he=Htab,holes=Holes}=We) ->
    Exclude = case Mirror of
		  none -> Holes;
		  _ -> ordsets:add_element(Mirror, Holes)
	      end,
    Faces = ordsets:subtract(gb_trees:keys(Ftab), Exclude),
    He0 = wings_face:to_edges(Exclude, We),
    He = gb_sets:union(gb_sets:from_list(He0), Htab),
    {Faces,He}.

%%%
%%% Calculation of face centers.
%%%

face_centers(Faces, We) ->
    face_centers(Faces, We, []).

face_centers([Face|Fs], We, Acc) ->
    Attrs = wings_va:face_mixed_attrs(Face, We),
    case wings_face:vertex_positions(Face, We) of
	[_,_] -> exit(foo);
	Positions ->
	    Center = wings_util:share(e3d_vec:average(Positions)),
	    face_centers(Fs, We, [{Face,{Center,Attrs,length(Positions)}}|Acc])
    end;
face_centers([], _We, Acc) -> reverse(Acc).

%%%
%%% Updating of the topology (edge and hard edge tables).
%%%

cut_edges(Es, Hard, #we{es=Etab0,he=Htab0,next_id=Id0}=We0) ->
    {Id,Etab,Htab} = cut_edges_1(Es, Hard, Id0, Etab0, Htab0),
    We = We0#we{es=Etab,he=Htab,next_id=Id},
    case wings_va:any_attributes(We) of
	false -> We;
	true -> cut_edges_attrs(Es, Id0, We0, We)
    end.

cut_edges_1([Edge|Es], Hard, NewEdge, Etab0, Htab0) ->
    Rec = array:get(Edge, Etab0),
    Etab = fast_cut(Edge, Rec, NewEdge, Etab0),
    case gb_sets:is_member(Edge, Hard) of
	true ->
	    Htab = case gb_sets:is_member(Edge, Htab0) of
		       true -> gb_sets:insert(NewEdge, Htab0);
		       false -> Htab0
		   end,
	    cut_edges_1(Es, Hard, NewEdge+1, Etab, Htab);
	false ->
	    cut_edges_1(Es, Hard, NewEdge+1, Etab, Htab0)
    end;
cut_edges_1([], _Hard, Id, Etab, Htab) ->
    {Id,Etab,Htab}.

fast_cut(Edge, Template, NewV=NewEdge, Etab0) ->
    #edge{ltpr=EdgeA,rtsu=EdgeB} = Template,
    NewEdgeRec = Template#edge{vs=NewV,ltsu=Edge,rtpr=Edge},
    Etab1 = array:set(NewEdge, NewEdgeRec, Etab0),
    EdgeRec = Template#edge{ve=NewV,rtsu=NewEdge,ltpr=NewEdge},
    Etab2 = array:set(Edge, EdgeRec, Etab1),
    Etab = wings_edge:patch_edge(EdgeA, NewEdge, Edge, Etab2),
    wings_edge:patch_edge(EdgeB, NewEdge, Edge, Etab).

cut_edges_attrs([Edge|Es], NewEdge, #we{es=Etab}=OrigWe, We0) ->
    #edge{lf=Lf,rf=Rf,ltpr=Ltpr,rtpr=Rtpr} = array:get(Edge, Etab),

    LeftAttrA = wings_va:edge_attrs(Edge, left, OrigWe),
    LeftAttrB =	wings_va:edge_attrs(Ltpr, Lf, OrigWe),
    AttrMidLeft = wings_va:average_attrs(LeftAttrA, LeftAttrB),

    AttrRightA = wings_va:edge_attrs(Edge, right, OrigWe),
    AttrRightB = wings_va:edge_attrs(Rtpr, Rf, OrigWe),
    AttrMidRight = wings_va:average_attrs(AttrRightA, AttrRightB),

    We1 = wings_va:set_edge_attrs(Edge, right, AttrMidRight, We0),
    We = wings_va:set_both_edge_attrs(NewEdge, AttrMidLeft, AttrRightA, We1),

    cut_edges_attrs(Es, NewEdge+1, OrigWe, We);
cut_edges_attrs([], _, _, We) -> We.

smooth_faces(FacePos, Id, We0) ->
    We1 = smooth_faces_1(FacePos, Id, We0),
    We = case wings_va:any_attributes(We1) of
	     false -> We1;
	     true -> smooth_faces_attrs(FacePos, Id, We0, We1)
	 end,
    case wings_we:is_open(We0) of
	false -> {We,[]};
	true -> {We,smooth_faces_hide(FacePos, We0)}
    end.

smooth_faces_1([{Face,{_,_,NumIds}}|Fs], Id, #we{es=Etab0}=We0) ->
    {Ids,We} = wings_we:new_wrap_range(NumIds, 1, We0),
    NewV = wings_we:id(0, Ids),
    Fun = smooth_edge_fun(Face, NewV, Id),
    {Etab,_} = face_fold(Fun, {Etab0,Ids}, Face, We),
    smooth_faces_1(Fs, Id, We#we{es=Etab});
smooth_faces_1([], _, We) ->
    We#we{fs=undefined}.

smooth_edge_fun(Face, NewV, Id) ->
    fun(Edge, Rec0, Next, {Etab0,Ids0}) ->
	    LeftEdge = RFace = wings_we:id(0, Ids0),
	    NewEdge = LFace = wings_we:id(1, Ids0),
	    RightEdge = wings_we:id(2, Ids0),
	    case Rec0 of
		#edge{ve=Vtx,rf=Face} when Vtx >= Id ->
		    Ids = Ids0,
		    Rec = Rec0#edge{rf=RFace,rtsu=NewEdge},
		    NewErec = #edge{vs=Vtx,ve=NewV,
				    rf=RFace,lf=LFace,
				    rtpr=Edge,rtsu=LeftEdge,
				    ltpr=RightEdge,ltsu=Next},
		    Etab1 = array:set(NewEdge, NewErec, Etab0);
		#edge{vs=Vtx,lf=Face} when Vtx >= Id ->
		    Ids = Ids0,
		    Rec = Rec0#edge{lf=RFace,ltsu=NewEdge},
		    NewErec = #edge{vs=Vtx,ve=NewV,
				    rf=RFace,lf=LFace,
				    rtpr=Edge,rtsu=LeftEdge,
				    ltpr=RightEdge,ltsu=Next},
		    Etab1 = array:set(NewEdge, NewErec, Etab0);
		#edge{vs=Vtx,rf=Face} when Vtx >= Id ->
		    Rec = Rec0#edge{rf=LFace,rtpr=NewEdge},
		    Etab1 = Etab0,
		    Ids = wings_we:bump_id(Ids0);
		#edge{ve=Vtx,lf=Face} when Vtx >= Id ->
		    Rec = Rec0#edge{lf=LFace,ltpr=NewEdge},
		    Etab1 = Etab0,
		    Ids = wings_we:bump_id(Ids0)
	    end,
	    Etab = array:set(Edge, Rec, Etab1),
	    {Etab,Ids}
    end.

smooth_faces_attrs([{Face,{_,Color,NumIds}}|Fs], Id, OrigWe0, We0) ->
    {Ids,OrigWe} = wings_we:new_wrap_range(NumIds, 1, OrigWe0),
    Fun = smooth_edge_fun_attrs(Face, Color, Id),
    {We,_} = face_fold(Fun, {We0,Ids}, Face, OrigWe),
    smooth_faces_attrs(Fs, Id, OrigWe, We);
smooth_faces_attrs([], _, _, We) -> We.

smooth_edge_fun_attrs(Face, Color, Id) ->
    fun(Edge, Rec0, _Next, {We0,Ids0}) ->
	    NewEdge = wings_we:id(1, Ids0),
	    case Rec0 of
		#edge{ve=Vtx,rf=Face} when Vtx >= Id ->
		    Ids = Ids0,
		    OldAttrs = wings_va:edge_attrs(Edge, right, We0),
		    We = wings_va:set_both_edge_attrs(NewEdge, OldAttrs, Color, We0);
		#edge{vs=Vtx,lf=Face} when Vtx >= Id ->
		    Ids = Ids0,
		    OldAttrs = wings_va:edge_attrs(Edge, left, We0),
		    We = wings_va:set_both_edge_attrs(NewEdge, OldAttrs, Color, We0);
		#edge{vs=Vtx,rf=Face} when Vtx >= Id ->
		    We = We0,
		    Ids = wings_we:bump_id(Ids0);
		#edge{ve=Vtx,lf=Face} when Vtx >= Id ->
		    We = We0,
		    Ids = wings_we:bump_id(Ids0)
	    end,
	    {We,Ids}
    end.

smooth_faces_hide(Fs, #we{next_id=Id}) ->
    smooth_faces_hide_1(Fs, Id, []).

smooth_faces_hide_1([{Face,{_,_,NumIds}}|Fs], Id, Acc) when Face >= 0 ->
    smooth_faces_hide_1(Fs, Id+NumIds, Acc);
smooth_faces_hide_1([{_,{_,_,NumIds}}|Fs], Id, Acc0) ->
    Acc = smooth_faces_hide_2(NumIds, Id, Acc0),
    smooth_faces_hide_1(Fs, Id+NumIds, Acc);
smooth_faces_hide_1([], _, Acc) -> Acc.

smooth_faces_hide_2(0, _, Acc) -> Acc;
smooth_faces_hide_2(N, Id, Acc) -> smooth_faces_hide_2(N-1, Id+1, [Id|Acc]).

face_fold(F, Acc, Face, #we{es=Etab,fs=Ftab}) ->
    Edge = gb_trees:get(Face, Ftab),
    face_fold(Edge, Etab, F, Acc, Face, Edge, not_done).

face_fold(LastEdge, _, _, Acc, _, LastEdge, done) -> Acc;
face_fold(Edge, Etab, F, Acc0, Face, LastEdge, _) ->
    case array:get(Edge, Etab) of
	#edge{lf=Face,ltsu=NextEdge}=E ->
	    Acc = F(Edge, E, NextEdge, Acc0),
	    face_fold(NextEdge, Etab, F, Acc, Face, LastEdge, done);
	#edge{rf=Face,rtsu=NextEdge}=E ->
	    Acc = F(Edge, E, NextEdge, Acc0),
	    face_fold(NextEdge, Etab, F, Acc, Face, LastEdge, done)
    end.

%%
%% XXX This is ugly. Here the materials are directly manpulated.
%%
smooth_materials(_, _, #we{mat=Mat}=We) when is_atom(Mat) -> We;
smooth_materials(Fs, FacePos, #we{fs=Ftab,mat=Mat0}=We) ->
    case length(Fs) =:= gb_trees:size(Ftab) of
	true ->				  %We are smoothing all faces.
	    smooth_materials_1(Mat0, FacePos, We, []);
	false ->		 %Must pick up the faces not smoothed.
	    Mat1 = sofs:from_external(Mat0, [{face,mat}]),
	    Changed = sofs:from_external(Fs, [face]),
	    {Mat2,Keep0} = sofs:partition(1, Mat1, Changed),
	    Mat = sofs:to_external(Mat2),
	    Keep = sofs:to_external(Keep0),
	    smooth_materials_1(Mat, FacePos, We, Keep)
    end.

smooth_materials_1(Fmat, Fpos, #we{next_id=Id}=We, Keep) ->
    Mat = smooth_materials_2(Fmat, Fpos, Id, Keep),
    We#we{mat=sort(Mat)}.

smooth_materials_2([{F,Mat}|Fs], [{F,{_,_,N}}|Fpos], Face, Acc0) ->
    NextFace = Face+N,
    Acc = smooth_materials_3(Mat, NextFace, Face, Acc0),
    smooth_materials_2(Fs, Fpos, NextFace, Acc);
smooth_materials_2([], [], _, Acc) -> Acc.

smooth_materials_3(_, Face, Face, Acc) -> Acc;
smooth_materials_3(Mat, NextFace, Face, Acc) ->
    smooth_materials_3(Mat, NextFace, Face+1, [{Face,Mat}|Acc]).

%%%
%%% Moving of vertices.
%%%

smooth_move_orig(EntireObject, Vs, FacePos, Htab, #we{vp=Vtab}=We, VtabTail) ->
    MoveFun = smooth_move_orig_fun(Vtab, FacePos, Htab),
    RevVtab =
	case EntireObject of
	    true ->
		smooth_move_orig_all(array:sparse_to_orddict(Vtab), MoveFun, We, []);
	    _ ->
		smooth_move_orig_some(Vs, array:sparse_to_orddict(Vtab), MoveFun, We, [])
	end,
    array:from_orddict(reverse(RevVtab, VtabTail)).

smooth_move_orig_all([{V,Pos0}|Vs], MoveFun, We, Acc) ->
    Pos = smooth_move_orig_1(V, Pos0, MoveFun, We),
    smooth_move_orig_all(Vs, MoveFun, We, [{V,Pos}|Acc]);
smooth_move_orig_all([], _FacePos, _MoveFun, Acc) -> Acc.

smooth_move_orig_some([V|Vs], [{V,Pos0}|Vs2], MoveFun, We, Acc) ->
    Pos = smooth_move_orig_1(V, Pos0, MoveFun, We),
    smooth_move_orig_some(Vs, Vs2, MoveFun, We, [{V,Pos}|Acc]);
smooth_move_orig_some(Vs, [Pair|Vs2], MoveFun, We, Acc) ->
    smooth_move_orig_some(Vs, Vs2, MoveFun, We, [Pair|Acc]);
smooth_move_orig_some([], [], _, _, Acc) -> Acc;
smooth_move_orig_some([], Vs2, _, _, Acc) -> reverse(Vs2, Acc).

smooth_move_orig_1(V, S, MoveFun, We) ->
    {_,Ps0,Hard} = wings_vertex:fold(MoveFun, {V,[],[]}, V, We),
    case length(Hard) of
	NumHard when NumHard < 2 ->
	    Ps = e3d_vec:add(Ps0),
	    {A,B} = case length(Ps0) of
			2*3 -> {1/9,1/3};
			2*4 -> {1/16,2/4};
			2*5 -> {1/25,3/5};
			N0 -> 
			    N = N0 bsr 1,
			    {1.0/(N*N),(N-2.0)/N}
		    end,
	    Pos = e3d_vec:add_prod(e3d_vec:mul(Ps, A), S, B),
	    wings_util:share(Pos);
	NumHard when NumHard =:= 2 ->
	    Pos0 = e3d_vec:add([e3d_vec:mul(S, 6.0)|Hard]),
	    Pos = e3d_vec:mul(Pos0, 1/8),
	    wings_util:share(Pos);
	_ThreeOrMore -> S
    end.

smooth_move_orig_fun(Vtab, FacePos, Htab) ->
    case gb_sets:is_empty(Htab) of
	true ->
	    fun(_Edge, Face, Erec, {V,Ps,_}) ->
		    %% No hard edges imply that all faces can be found
		    %% in the FacePos table. Therefore gb_trees:get/2 is safe.
		    OPos = wings_vertex:other_pos(V, Erec, Vtab),
		    FPos = gb_trees:get(Face, FacePos),
		    {V,[OPos,FPos|Ps],[]}
	    end;
	false ->
	    fun(Edge, Face, Erec, {V,Ps0,Hard0}) ->
		    OPos = wings_vertex:other_pos(V, Erec, Vtab),
		    FPos = case gb_trees:lookup(Face, FacePos) of
			       none -> none;
			       {value,FPos0} -> FPos0
			   end,
		    Ps = [FPos,OPos|Ps0],
		    Es = case gb_sets:is_member(Edge, Htab) of
			     true -> [OPos|Hard0];
			     false -> Hard0
			 end,
		    {V,Ps,Es}
	    end
    end.

update_edge_vs_all(#we{es=Etab}, FacePos, Hard, Vtab, V) ->
    update_edge_vs_all(array:sparse_to_orddict(Etab),
		       FacePos, Hard, Vtab, V, []).

update_edge_vs_all([{Edge,Rec}|Es], FacePos, Hard, Vtab, V, Acc) ->
    Pos = update_edge_vs_1(Edge, Hard, Rec, FacePos, Vtab),
    update_edge_vs_all(Es, FacePos, Hard, Vtab, V+1, [{V,Pos}|Acc]);
update_edge_vs_all([], _, _, _, V, Acc) ->
    {Acc,V}.

update_edge_vs_some(Es, #we{es=Etab}, FacePos, Hard, Vtab, V) ->
    update_edge_vs_some(Es, Etab, FacePos, Hard, Vtab, V, []).

update_edge_vs_some([E|Es], Etab, FacePos, Hard, Vtab, V, Acc) ->
    Rec = array:get(E, Etab),
    Pos = update_edge_vs_1(E, Hard, Rec, FacePos, Vtab),
    update_edge_vs_some(Es, Etab, FacePos, Hard, Vtab, V+1, [{V,Pos}|Acc]);
update_edge_vs_some([], _, _, _, _, V, Acc) ->
    {Acc,V}.

update_edge_vs_1(Edge, Hard, Rec, FacePos, Vtab) ->
    case gb_sets:is_member(Edge, Hard) of
	true ->
	    #edge{vs=Va,ve=Vb} = Rec,
	    e3d_vec:average(array:get(Va, Vtab), array:get(Vb, Vtab));
	false ->
	    #edge{vs=Va,ve=Vb,lf=Lf,rf=Rf} = Rec,
	    LfPos = gb_trees:get(Lf, FacePos),
	    RfPos = gb_trees:get(Rf, FacePos),
	    Pos0 = e3d_vec:average(array:get(Va, Vtab),
				   array:get(Vb, Vtab),
				   LfPos, RfPos),
	    wings_util:share(Pos0)
    end.

smooth_new_vs([{_,{Center,_,NumIds}}|Fs], V, Acc) ->
    smooth_new_vs(Fs, V+NumIds, [{V,Center}|Acc]);
smooth_new_vs([], _, Acc) -> reverse(Acc).
