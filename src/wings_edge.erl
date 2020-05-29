%%
%%  wings_edge.erl --
%%
%%     This module contains most edge command and edge utility functions.
%%
%%  Copyright (c) 2001-2011 Bjorn Gustavsson.
%%
%%  See the file "license.terms" for information on usage and redistribution
%%  of this file, and for a DISCLAIMER OF ALL WARRANTIES.
%%
%%     $Id$
%%

-module(wings_edge).

%% Utilities.
-export([from_vs/2,to_vertices/2,from_faces/2,
         reachable_faces/3,
	 cut/3,fast_cut/3,screaming_cut/3,
	 dissolve_edge/2,dissolve_edges/2,dissolve_edges/3,
         dissolve_isolated_vs/2,
	 hardness/3,
	 patch_edge/4,patch_edge/5,
	 length/2
	]).

-export_type([edge_num/0]).

-include("wings.hrl").
-import(lists, [foldl/3,sort/1]).

-type edge_num() :: non_neg_integer().

length(Ei, #we{es=Etab,vp=VPos}) ->
    #edge{vs=VS,ve=VE} = array:get(Ei,Etab),
    Pt1 = array:get(VS,VPos),
    Pt2 = array:get(VE,VPos),
    e3d_vec:dist(Pt1,Pt2).

from_vs(Vs, We) when is_list(Vs) ->
    from_vs(Vs, We, []);
from_vs(Vs, We) ->
    gb_sets:from_list(from_vs(gb_sets:to_list(Vs), We, [])).

from_vs([V|Vs], We, Acc0) ->
    Acc = wings_vertex:fold(fun(E, _, _, A) -> [E|A] end, Acc0, V, We),
    from_vs(Vs, We, Acc);
from_vs([], _, Acc) -> Acc.

%% to_vertices(EdgeGbSet, We) -> VertexGbSet
%%  Convert a set of edges to a set of vertices.

to_vertices(Edges, #we{es=Etab}) when is_list(Edges) ->
    to_vertices(Edges, Etab, []);
to_vertices(Edges, #we{es=Etab}) ->
    to_vertices(gb_sets:to_list(Edges), Etab, []).

to_vertices([E|Es], Etab, Acc) ->
    #edge{vs=Va,ve=Vb} = array:get(E, Etab),
    to_vertices(Es, Etab, [Va,Vb|Acc]);
to_vertices([], _Etab, Acc) -> ordsets:from_list(Acc).

%% from_faces(FaceSet, We) -> EdgeSet
%%  Convert faces to edges.
from_faces(Faces, We) ->
    gb_sets:from_ordset(wings_face:to_edges(Faces, We)).

%% cut(Edge, Parts, We0) -> {We,NewVertex,NewEdge}
%%  Cut an edge into Parts parts.
cut(Edge, 2, We) ->
    fast_cut(Edge, default, We);
cut(Edge, N, #we{es=Etab}=We) ->
    #edge{vs=Va,ve=Vb} = array:get(Edge, Etab),
    PosA = wings_vertex:pos(Va, We),
    PosB = wings_vertex:pos(Vb, We),
    Vec = e3d_vec:mul(e3d_vec:sub(PosB, PosA), 1/N),
    cut_1(N, Edge, PosA, Vec, We).

%% fast_cut(Edge, Position, We0) -> {We,NewElement}
%%      NewElement = ID for the new vertex and the new Edge
%%  Cut an edge in two parts. Position can be given as
%%  the atom `default', in which case the position will
%%  be set to the midpoint of the edge.

fast_cut(Edge, Pos0, We0) ->
    {NewEdge=NewV,We1} = wings_we:new_ids(1, We0),
    #we{es=Etab0,vc=Vct0,vp=Vtab0,he=Htab0} = We1,
    Template = array:get(Edge, Etab0),
    #edge{vs=Vstart,ve=Vend,ltpr=EdgeA,rtsu=EdgeB} = Template,
    VendPos = array:get(Vend, Vtab0),
    Vct1 = array:set(Vend, NewEdge, Vct0),
    VstartPos = wings_vertex:pos(Vstart, Vtab0),
    if
	Pos0 =:= default ->
	    NewVPos0 = e3d_vec:average(VstartPos, VendPos);
	true ->
	    NewVPos0 = Pos0
    end,
    NewVPos = wings_util:share(NewVPos0),
    Vct = array:set(NewV, NewEdge, Vct1),
    Vtab = array:set(NewV, NewVPos, Vtab0),

    NewEdgeRec = Template#edge{vs=NewV,ltsu=Edge,rtpr=Edge},
    Etab1 = array:set(NewEdge, NewEdgeRec, Etab0),
    Etab2 = patch_edge(EdgeA, NewEdge, Edge, Etab1),
    Etab3 = patch_edge(EdgeB, NewEdge, Edge, Etab2),
    EdgeRec = Template#edge{ve=NewV,rtsu=NewEdge,ltpr=NewEdge},
    Etab = array:set(Edge, EdgeRec, Etab3),
    Htab = case gb_sets:is_member(Edge, Htab0) of
	       false -> Htab0;
	       true -> gb_sets:insert(NewEdge, Htab0)
	   end,
    We2 = We1#we{es=Etab,vc=Vct,vp=Vtab,he=Htab},

    %% Now interpolate and set vertex attributes.
    Weight = if
		 Pos0 =:= default -> 0.5;
		 VstartPos =:= VendPos -> 0.5;
		 Pos0 =:= VstartPos -> 0.0;
		 Pos0 =:= VendPos -> 1.0;
		 true ->
		     ADist = e3d_vec:dist(Pos0, VstartPos),
		     BDist = e3d_vec:dist(Pos0, VendPos),
		     ADist/(ADist+BDist)
	     end,
    AttrMidLeft = wings_va:edge_attrs(Edge, left, Weight, We1),
    AttrMidRight = wings_va:edge_attrs(Edge, right, Weight, We1),
    AttrEndLeft = wings_va:edge_attrs(Edge, right, We1),

    We3 = wings_va:set_edge_attrs(Edge, right, AttrMidRight, We2),
    We = wings_va:set_both_edge_attrs(NewEdge, AttrMidLeft, AttrEndLeft, We3),

    {We,NewV}.

%% screaming_cut(Edge, Position, We0) -> {We,NewVertex,NewEdge}
%%  Cut an edge in two parts screamlingly fast. Does not handle
%%  vertex colors or UV coordinates.

screaming_cut(Edge, NewVPos, We0) ->
    {NewEdge=NewV,We} = wings_we:new_ids(1, We0),
    #we{es=Etab0,vc=Vct0,vp=Vtab0,he=Htab0} = We,
    Template = array:get(Edge, Etab0),
    #edge{ve=Vend,ltpr=EdgeA,rtsu=EdgeB} = Template,
    Vct1 = array:set(Vend, NewEdge, Vct0),
    Vct = array:set(NewV, NewEdge, Vct1),
    Vtab = array:set(NewV, NewVPos, Vtab0),

    NewEdgeRec = Template#edge{vs=NewV,ltsu=Edge,rtpr=Edge},
    Etab1 = array:set(NewEdge, NewEdgeRec, Etab0),
    Etab2 = patch_edge(EdgeA, NewEdge, Edge, Etab1),
    Etab3 = patch_edge(EdgeB, NewEdge, Edge, Etab2),
    EdgeRec = Template#edge{ve=NewV,rtsu=NewEdge,ltpr=NewEdge},
    Etab = array:set(Edge, EdgeRec, Etab3),

    Htab = case gb_sets:is_member(Edge, Htab0) of
	       false -> Htab0;
	       true -> gb_sets:insert(NewEdge, Htab0)
	   end,
    {We#we{es=Etab,vc=Vct,vp=Vtab,he=Htab},NewV}.

%%%
%%% Dissolve.
%%%

dissolve_edge(Edge, We) ->
    dissolve_edges([Edge], We).

dissolve_edges(Edges, We0) when is_list(Edges) ->
    Faces = gb_sets:to_list(wings_face:from_edges(Edges, We0)),
    case dissolve_edges(Edges, Faces, We0) of
        {We,[]} -> We;
        {_We, _Bad} -> exit("Dissolving would cause a badly formed face.")
    end;
dissolve_edges(Edges, We) ->
    dissolve_edges(gb_sets:to_list(Edges), We).


%% dissolve_isolated_vs([Vertex], We) -> We'
%%  Remove all isolated vertices ("winged vertices", or vertices
%%  having exactly two edges).
dissolve_isolated_vs([_|_]=Vs, We) ->
    dissolve_isolated_vs_1(Vs, We, []);
dissolve_isolated_vs([], We) -> We.

%%%
%%% Setting hard/soft edges.
%%%

hardness(Edge, soft, Htab) -> gb_sets:delete_any(Edge, Htab);
hardness(Edge, hard, Htab) -> gb_sets:add(Edge, Htab).

%%
%% Collect all faces reachable from Face, without crossing
%% any of the edges in Edges.
%%

-spec reachable_faces(InFaces, Edges, We) -> Faces when
      InFaces :: [wings_face:face_num()] | gb_sets:set(wings_face:face_num()),
      Edges :: wings_sel:edge_set(),
      We :: #we{},
      Faces :: wings_sel:face_set().

reachable_faces(Faces, Edges, We) when is_list(Faces) ->
    collect_faces(gb_sets:from_list(Faces), We, Edges, gb_sets:empty());
reachable_faces(Fs, Edges, We) ->
    collect_faces(Fs, We, Edges, gb_sets:empty()).


%%%
%%% Local functions
%%%

cut_1(2, Edge, _, _, We) ->
    fast_cut(Edge, default, We);
cut_1(N, Edge, Pos0, Vec, We0) ->
    Pos = e3d_vec:add(Pos0, Vec),
    {We,NewE} = fast_cut(Edge, Pos, We0),
    cut_1(N-1, NewE, Pos, Vec, We).

%%% Dissolving edges.

dissolve_edges(Edges0, Faces, We0) when is_list(Edges0) ->
    #we{es=Etab} = We1 = foldl(fun internal_dissolve_edge/2, We0, Edges0),
    case [E || E <- Edges0, array:get(E, Etab) =/= undefined] of
        Edges0 ->
            %% No edge was deleted in the last pass. We are done.
            We2 = wings_we:rebuild(We0),
            #we{fs=Ftab}=We = wings_we:validate_mirror(We2),
            Bad = lists:filter(
                    fun(Face) ->
                            gb_trees:is_defined(Face, Ftab) andalso
                                not wings_we:is_face_consistent(Face, We)
                    end, Faces),
            {We, Bad};
        Edges ->
            dissolve_edges(Edges, Faces, We1)
    end.

internal_dissolve_edge(Edge, #we{es=Etab}=We0) ->
    case array:get(Edge, Etab) of
	undefined -> We0;
	#edge{ltpr=Same,ltsu=Same,rtpr=Same,rtsu=Same} ->
	    EmptyGbTree = gb_trees:empty(),
	    Empty = array:new(),
	    We0#we{vc=Empty,vp=Empty,es=Empty,fs=EmptyGbTree,he=gb_sets:empty(),holes=[]};
	#edge{rtpr=Back,ltsu=Back}=Rec ->
	    merge_edges(backward, Edge, Rec, We0);
	#edge{rtsu=Forward,ltpr=Forward}=Rec ->
	    merge_edges(forward, Edge, Rec, We0);
	Rec ->
	    try dissolve_edge_1(Edge, Rec, We0) of
		We -> We
	    catch
		throw:hole -> We0
	    end
    end.

%% dissolve_edge_1(Edge, EdgeRecord, We) -> We
%%  Remove an edge and a face. If one of the faces is degenerated
%%  (only consists of two edges), remove that one. If no face is
%%  degenerated, prefer to keep an invisible face (if an edge
%%  bordering a hole is dissolved, we except except the hole to
%%  expand). Otherwise, it does not matter which face we keep.
%%
dissolve_edge_1(Edge, #edge{lf=Remove,rf=Keep,ltpr=Same,ltsu=Same}=Rec, We) ->
    dissolve_edge_2(Edge, Remove, Keep, Rec, We);
dissolve_edge_1(Edge, #edge{lf=Keep,rf=Remove,rtpr=Same,rtsu=Same}=Rec, We) ->
    dissolve_edge_2(Edge, Remove, Keep, Rec, We);
dissolve_edge_1(Edge, #edge{lf=Lf,rf=Rf}=Rec, We) ->
    if
	Lf < 0 ->
	    %% Keep left face.
	    if
		Rf < 0 ->
		    %% The right face is also hidden. (Probably unusual
		    %% in practice.) It might also be a hole.
		    Holes = ordsets:del_element(Rf, We#we.holes),
		    dissolve_edge_2(Edge, Rf, Lf, Rec, We#we{holes=Holes});
		true ->
		    dissolve_edge_2(Edge, Rf, Lf, Rec, We)
	    end;
	Rf < 0 ->
	    %% Keep the right face. Remove the (visible) left face.
	    dissolve_edge_2(Edge, Lf, Rf, Rec, We);
	true ->
	    %% It does not matter which one we keep.
	    dissolve_edge_2(Edge, Rf, Lf, Rec, We)
    end.

dissolve_edge_2(Edge, FaceRemove, FaceKeep,
		#edge{vs=Va,ve=Vb,ltpr=LP,ltsu=LS,rtpr=RP,rtsu=RS},
		#we{fs=Ftab0,es=Etab0,vc=Vct0,he=Htab0,holes=Holes0}=We0) ->
    %% First change the face for all edges surrounding the face we will remove.
    Etab1 = wings_face:fold(
	      fun (_, E, _, IntEtab) when E =:= Edge -> IntEtab;
		  (_, E, R, IntEtab) ->
		      case R of
			  #edge{lf=FaceRemove,rf=FaceKeep} ->
			      throw(hole);
			  #edge{rf=FaceRemove,lf=FaceKeep} ->
			      throw(hole);
			  #edge{lf=FaceRemove} ->
			      array:set(E, R#edge{lf=FaceKeep}, IntEtab);
			  #edge{rf=FaceRemove} ->
			      array:set(E, R#edge{rf=FaceKeep}, IntEtab)
		      end
	      end, Etab0, FaceRemove, We0),

    %% Patch all predecessors and successor of the edge we will remove.
    Etab2 = patch_edge(LP, RS, Edge, Etab1),
    Etab3 = patch_edge(LS, RP, Edge, Etab2),
    Etab4 = patch_edge(RP, LS, Edge, Etab3),
    Etab5 = patch_edge(RS, LP, Edge, Etab4),

    %% Remove the edge.
    Etab = array:reset(Edge, Etab5),
    Htab = hardness(Edge, soft, Htab0),

    %% Update the incident vertex table for both vertices
    %% to make sure they point to the correct existing edges.
    %%
    %% We used to simply set the 'vc' field to 'undefined' to
    %% force a complete rebuild of the vertex table, but that
    %% could cause Extrude (for regions) to become slow for certain
    %% selection shapes, as the Extrude command internally does a
    %% collapse of one edge in a triangle face, which in turns causes
    %% a dissolve of one of the remaining edges.
    Vct = case Vct0 of
	      undefined ->
		  Vct0;
	      _ ->
		  %% For the vertices Va and Vb, pick one of the still existing
		  %% edges emanating from the vertex.
		  %%
		  %% The edges LS ('ltsu') and RP ('rtpr') emanate from Va ('vs').
		  %% The edges LP ('ltpr') and RS ('rtsu') emanate from Vb ('ve').
		  Vct1 = array:set(Va, LS, Vct0),
		  array:set(Vb, RS, Vct1)
	  end,

    %% Remove the face. Update the incident face to make sure
    %% the face points to an existing edge.
    Ftab1 = gb_trees:delete(FaceRemove, Ftab0),
    We1 = wings_facemat:delete_face(FaceRemove, We0),
    AnEdge = LP,
    Ftab = gb_trees:update(FaceKeep, AnEdge, Ftab1),

    %% It is probably unusual that 2 edge face is a hole,
    %% but it can happens.
    Holes = ordsets:del_element(FaceRemove, Holes0),

    %% Store all updated tables.
    We = We1#we{es=Etab,fs=Ftab,vc=Vct,he=Htab,holes=Holes},

    %% If the kept face (FaceKeep) has become a two-edge face,
    %% we must get rid of that face by dissolving one of its edges.
    case array:get(AnEdge, Etab) of
	#edge{lf=FaceKeep,ltpr=Same,ltsu=Same} ->
	    internal_dissolve_edge(AnEdge, We);
	#edge{rf=FaceKeep,rtpr=Same,rtsu=Same} ->
	    internal_dissolve_edge(AnEdge, We);
	_Other -> We
    end.

%% Since the dissolve operation will not keep the incident
%% edge table for vertices updated, we'll need to lookup
%% all incident edges now before we have started to dissolve.
dissolve_isolated_vs_1([V|Vs], #we{vc=Vct}=We, Acc) ->
    case array:get(V, Vct) of
	undefined ->
	    %% A previous pass has already removed this vertex.
	    dissolve_isolated_vs_1(Vs, We, Acc);
	Edge ->
	    dissolve_isolated_vs_1(Vs, We, [{V,Edge}|Acc])
    end;
dissolve_isolated_vs_1([], We, Vc) ->
    dissolve_isolated_vs_2(Vc, We, []).

%% Now do all dissolving.
dissolve_isolated_vs_2([{V,Edge}|T], We0, Acc) ->
    case dissolve_vertex(V, Edge, We0) of
	done -> dissolve_isolated_vs_2(T, We0, Acc);
	We -> dissolve_isolated_vs_2(T, We, [V|Acc])
    end;
dissolve_isolated_vs_2([], We, []) ->
    %% Nothing was done in the last pass. We don't need to do a vertex GC.
    We;
dissolve_isolated_vs_2([], We0, Vs) ->
    We = wings_we:rebuild(We0#we{vc=undefined}),

    %% Now do another pass over the vertices still in our list.
    %% Reason:
    %%
    %% 1. An incident edge may have become wrong by a previous
    %%    dissolve (on another vertex). Do another try now that
    %%    the incident table has been rebuilt.
    %%
    %% 2. A vertex may have be connected to two faces that
    %%    have no edge in common. In that case, all edges
    %%    are not reachable from the incident edge.
    dissolve_isolated_vs(Vs, We).

%% dissolve(V, Edge, We0) -> We|done
%%  Dissolve the given vertex. The 'done' return value means
%%  that the vertex is already non-existing (or is not isolated).
%%  If a We is returned, the caller must call this function again
%%  (after rebuilding the incident table) since there might be more
%%  work to do.
dissolve_vertex(V, Edge, #we{es=Etab}=We0) ->
    case array:get(Edge, Etab) of
	#edge{vs=V,ltsu=AnEdge,rtpr=AnEdge}=Rec ->
	    merge_edges(backward, Edge, Rec, We0);
	#edge{ve=V,rtsu=AnEdge,ltpr=AnEdge}=Rec ->
	    merge_edges(forward, Edge, Rec, We0);

	%% Handle the case that the incident edge is correct for
	%% the given vertex, but the vertex is NOT isolated.
	#edge{vs=V} -> done;
	#edge{ve=V} -> done;

	%% The incident edge is either non-existing or no longer
	%% references the given edge. In this case, we'll need
	%% to try dissolving the vertex again in the next
	%% pass after the incident table has been rebuilt.
	undefined -> We0;
	_ -> We0
    end.

%%
%% We like winged edges, but not winged vertices (a vertex with
%% only two edges connected to it). We will remove the winged vertex
%% by joining the two edges connected to it.
%%

merge_edges(Dir, Edge, Rec, #we{es=Etab}=We) ->
    {Va,Vb,_,_,To,To} = half_edge(Dir, Rec),
    case array:get(To, Etab) of
	#edge{vs=Va,ve=Vb} ->
	    del_2edge_face(Dir, Edge, Rec, To, We);
	#edge{vs=Vb,ve=Va} ->
	    del_2edge_face(Dir, Edge, Rec, To, We);
	_Other ->
	    merge_1(Dir, Edge, Rec, To, We)
    end.

merge_1(Dir, Edge, Rec, To, #we{es=Etab0,fs=Ftab0,he=Htab0}=We0) ->
    OtherDir = reverse_dir(Dir),
    {Vkeep,Vdelete,Lf,Rf,L,R} = half_edge(OtherDir, Rec),
    Etab1 = patch_edge(L, To, Edge, Etab0),
    Etab2 = patch_edge(R, To, Edge, Etab1),
    Etab3 = patch_half_edge(To, Vkeep, Lf, L, Rf, R, Vdelete, Etab2),
    Htab = hardness(Edge, soft, Htab0),
    Etab = array:reset(Edge, Etab3),
    #edge{lf=Lf,rf=Rf} = Rec,
    Ftab1 = update_face(Lf, To, Edge, Ftab0),
    Ftab = update_face(Rf, To, Edge, Ftab1),
    We1 = We0#we{es=Etab,fs=Ftab,he=Htab,vc=undefined},
    We = case {wings_va:any_attributes(We1),Dir} of
	     {false,_} ->
		 We1;
	     {_,backward} ->
		 Attr = wings_va:edge_attrs(Edge, right, We0),
		 We2 = wings_va:set_edge_attrs(To, Rf, Attr, We1),
		 wings_va:del_edge_attrs(Edge, We2);
	     {_,forward} ->
		 Attr = wings_va:edge_attrs(Edge, left, We0),
		 We2 = wings_va:set_edge_attrs(To, Lf, Attr, We1),
		 wings_va:del_edge_attrs(Edge, We2)
	 end,
    merge_2(To, We).

merge_2(Edge, #we{es=Etab}=We) ->
    %% If the merged edge is part of a two-edge face, we must
    %% remove that edge too.
    case array:get(Edge, Etab) of
	#edge{ltpr=Same,ltsu=Same} ->
	    internal_dissolve_edge(Edge, We);
	#edge{rtpr=Same,rtsu=Same} ->
	    internal_dissolve_edge(Edge, We);
	_Other -> We
    end.

update_face(Face, Edge, OldEdge, Ftab) ->
    case gb_trees:get(Face, Ftab) of
	OldEdge -> gb_trees:update(Face, Edge, Ftab);
	_Other -> Ftab
    end.

del_2edge_face(Dir, EdgeA, RecA, EdgeB,
	       #we{es=Etab0,fs=Ftab0,he=Htab0,holes=Holes0}=We) ->
    {_,_,Lf,Rf,_,_} = half_edge(reverse_dir(Dir), RecA),
    RecB = array:get(EdgeB, Etab0),
    Del = gb_sets:from_list([EdgeA,EdgeB]),
    EdgeANear = stabile_neighbor(RecA, Del),
    EdgeBNear = stabile_neighbor(RecB, Del),
    Etab1 = patch_edge(EdgeANear, EdgeBNear, EdgeA, Etab0),
    Etab2 = patch_edge(EdgeBNear, EdgeANear, EdgeB, Etab1),
    Etab3 = array:reset(EdgeA, Etab2),
    Etab = array:reset(EdgeB, Etab3),

    %% Patch hardness table.
    Htab1 = hardness(EdgeA, soft, Htab0),
    Htab = hardness(EdgeB, soft, Htab1),

    %% Patch the face table.
    #edge{lf=Klf,rf=Krf} = array:get(EdgeANear, Etab),
    KeepFaces = ordsets:from_list([Klf,Krf]),
    EdgeAFaces = ordsets:from_list([Lf,Rf]),
    [DelFace] = ordsets:subtract(EdgeAFaces, KeepFaces),
    Ftab1 = gb_trees:delete(DelFace, Ftab0),
    [KeepFace] = ordsets:intersection(KeepFaces, EdgeAFaces),
    Ftab2 = update_face(KeepFace, EdgeANear, EdgeA, Ftab1),
    Ftab = update_face(KeepFace, EdgeBNear, EdgeB, Ftab2),

    %% It is probably unusual that 2 edge face is a hole,
    %% but better safe than sorry.
    Holes = ordsets:del_element(DelFace, Holes0),

    %% Return result.
    We#we{vc=undefined,es=Etab,fs=Ftab,he=Htab,holes=Holes}.

stabile_neighbor(#edge{ltpr=Ea,ltsu=Eb,rtpr=Ec,rtsu=Ed}, Del) ->
    [Edge] = foldl(fun(E, A) ->
			   case gb_sets:is_member(E, Del) of
			       true -> A;
			       false -> [E|A]
			   end
		   end, [], [Ea,Eb,Ec,Ed]),
    Edge.


collect_faces(Work0, We, Edges, Acc0) ->
    case gb_sets:is_empty(Work0) of
	true -> Acc0;
	false ->
	    {Face,Work1} = gb_sets:take_smallest(Work0),
	    Acc = gb_sets:insert(Face, Acc0),
	    Work = collect_maybe_add(Work1, Face, Edges, We, Acc),
	    collect_faces(Work, We, Edges, Acc)
    end.

collect_maybe_add(Work, Face, Edges, We, Res) ->
    wings_face:fold(
      fun(_, Edge, Rec, A) ->
	      case gb_sets:is_member(Edge, Edges) of
		  true -> A;
		  false ->
		      Of = wings_face:other(Face, Rec),
		      case gb_sets:is_member(Of, Res) of
			  true -> A;
			  false -> gb_sets:add(Of, A)
		      end
	      end
      end, Work, Face, We).

%%% Edge ring functions.

-record(r,{id,l,r,
	   ls=gb_sets:empty(),
	   rs=gb_sets:empty()}).

opposing_edge(Edge, #we{es=Es}=We, Side) ->
    #edge{lf=Left,rf=Right} = array:get(Edge, Es),
    Face = case Side of
               left -> Left;
               right -> Right
           end,
    %% Get opposing edge or fail.
    case wings_face:vertices(Face, We) of
        4 -> next_edge(next_edge(Edge, Face, We), Face, We);
        _ -> unknown
    end.

next_edge(Edge, Face, #we{es=Etab})->
    case array:get(Edge, Etab) of
        #edge{lf=Face,ltsu=NextEdge} -> NextEdge;
        #edge{rf=Face,rtsu=NextEdge} -> NextEdge
    end.


%%%
%%% Utilities.
%%%

reverse_dir(forward) -> backward;
reverse_dir(backward) -> forward.

half_edge(backward, #edge{vs=Va,ve=Vb,lf=Lf,rf=Rf,ltsu=L,rtpr=R}) ->
    {Va,Vb,Lf,Rf,L,R};
half_edge(forward, #edge{ve=Va,vs=Vb,lf=Lf,rf=Rf,ltpr=L,rtsu=R}) ->
    {Va,Vb,Lf,Rf,L,R}.

patch_half_edge(Edge, V, FaceA, Ea, FaceB, Eb, OrigV, Etab) ->
    New = case array:get(Edge, Etab) of
	      #edge{vs=OrigV,lf=FaceA,rf=FaceB}=Rec ->
		  Rec#edge{vs=V,ltsu=Ea,rtpr=Eb};
	      #edge{vs=OrigV,lf=FaceB,rf=FaceA}=Rec ->
		  Rec#edge{vs=V,ltsu=Eb,rtpr=Ea};
	      #edge{ve=OrigV,lf=FaceA,rf=FaceB}=Rec ->
		  Rec#edge{ve=V,ltpr=Ea,rtsu=Eb};
	      #edge{ve=OrigV,lf=FaceB,rf=FaceA}=Rec ->
		  Rec#edge{ve=V,ltpr=Eb,rtsu=Ea}
	  end,
    array:set(Edge, New, Etab).

patch_edge(Edge, ToEdge, OrigEdge, Etab) ->
    New = case array:get(Edge, Etab) of
	      #edge{ltsu=OrigEdge}=R ->
		  R#edge{ltsu=ToEdge};
	      #edge{ltpr=OrigEdge}=R ->
		  R#edge{ltpr=ToEdge};
	      #edge{rtsu=OrigEdge}=R ->
		  R#edge{rtsu=ToEdge};
	      #edge{rtpr=OrigEdge}=R ->
		  R#edge{rtpr=ToEdge}
	  end,
    array:set(Edge, New, Etab).

patch_edge(Edge, ToEdge, Face, OrigEdge, Etab) ->
    New = case array:get(Edge, Etab) of
	      #edge{lf=Face,ltsu=OrigEdge}=R ->
		  R#edge{ltsu=ToEdge};
	      #edge{lf=Face,ltpr=OrigEdge}=R ->
		  R#edge{ltpr=ToEdge};
	      #edge{rf=Face,rtsu=OrigEdge}=R ->
		  R#edge{rtsu=ToEdge};
	      #edge{rf=Face,rtpr=OrigEdge}=R ->
		  R#edge{rtpr=ToEdge}
	  end,
    array:set(Edge, New, Etab).

