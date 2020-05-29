%%
%%  wings.hrl --
%%
%%     Global record definition and defines.
%%
%%  Copyright (c) 2001-2011 Bjorn Gustavsson
%%
%%  See the file "license.terms" for information on usage and redistribution
%%  of this file, and for a DISCLAIMER OF ALL WARRANTIES.
%%
%%     $Id$
%%

-define(F32,  32/float-native).
-define(I32,  32/signed-native).
-define(UI32, 32/native).

-record(io,
	{grab_stack=[],				%Grab stack.
	 key_up=false                          %Subscribed to key_up
	}).

-define(EVENT_QUEUE, wings_io_event_queue).

-define(TC(Cmd), wings_util:tc(fun() -> Cmd end, ?MODULE, ?LINE)).

-define(dbg(Str,Args), io:format("~p:~p: " ++ Str, [?MODULE,?LINE|Args])).

%%
%% Types.
%%

-type bounding_box() :: [{float(),float(),float()}].

-type wings_cmd() :: tuple() | atom().
-type maybe_wings_cmd() :: 'ignore' | wings_cmd().

-type wings_vtx_buffer() :: 'none' | {integer(),integer()}.

-type selection() :: orddict:orddict(integer(),gb_sets:set()).


%% The Winged-Edge data structure.
%% See http://www.cs.mtu.edu/~shene/COURSES/cs3621/NOTES/model/winged-e.html
-record(we,
	{id :: non_neg_integer()|undefined,	%Shape id. (undefined during construction)
	 perm=0 :: wings_we:perm(),             %See wings_we.erl.
	 name="" :: string() | tuple(),		%Name. (AutoUV stores other things here.)
	 es=array:new() :: array:array(),	%array containing edges
	 lv=none :: 'none' | array:array(),	%Left vertex attributes
	 rv=none :: 'none' | array:array(),	%Right vertex attributes,
	 fs :: gb_trees:tree() | undefined,	%Faces (undefined during construction)
	 he=gb_sets:empty() :: gb_sets:set(),	%Hard edges
	 vc :: array:array() | undefined,       %Connection info (=incident edge)
						% for vertices. (undefined during re-construction)
	 vp=array:new() :: array:array(),	%Vertex positions.
	 pst=gb_trees:empty(),                  %Plugin State Info, 
						%   gb_tree where key is plugin module
	 mat=default,				%Materials.
	 next_id=0 :: non_neg_integer(),	%Next free ID for vertices,
						% edges, and faces.
						% (Needed because we never re-use
						%  IDs.)
	 mirror=none :: 'none' | non_neg_integer(),	%Mirror: none|Face
	 light=none,				%Light data: none|Light
	 holes=[] :: [integer()],		%List of hole faces.
         temp=[] :: term()
	}).

-define(IS_VISIBLE(Perm), (Perm =< 1)).
-define(IS_NOT_VISIBLE(Perm), (Perm > 1)).
-define(IS_SELECTABLE(Perm), (Perm =:= 0)).
-define(IS_NOT_SELECTABLE(Perm), (Perm =/= 0)).

-define(PERM_LOCKED_BIT, 1).
-define(PERM_HIDDEN_BIT, 2).

%%
%% Macros for testing for lights. We don't want to put the record
%% definition for the light record here (to discourage plug-in
%% writes bypassing the API in wings_light), so we'll depend on
%% the type of light to be in the second element of the tuple.
%%
-define(IS_ANY_LIGHT(We), (We#we.light =/= none)).
-define(IS_LIGHT(We), (We#we.light =/= none andalso
		       element(2, We#we.light) =/= area)).
-define(IS_AREA_LIGHT(We), (We#we.light =/= none andalso
			    element(2, We#we.light) =:= area)).

%% Edge in a winged-edge object.
%%
%%                \       /           
%%                 \     /            
%%            ltpr  \   / rtsu        
%%                   \ /              
%%                   ve  b            
%%                    |               
%%                    |               
%%       lf           |          rf   
%%                    |               
%%                    |               
%%                 a  vs              
%%                   / \              
%%            ltsu  /   \ rtpr        
%%                 /     \            
%%                /       \           
%%                               	   
-record(edge,
	{vs=0   :: wings_vertex:vertex_num(),     %Start vertex for edge
	 ve=0   :: wings_vertex:vertex_num(),     %End vertex for edge
	 lf=0   :: wings_face:face_num(),         %Left face
	 rf=0   :: wings_face:face_num(),         %Right face
	 ltpr=0 :: wings_edge:edge_num(), %Left traversal predecessor
	 ltsu=0 :: wings_edge:edge_num(), %Left traversal successor
	 rtpr=0 :: wings_edge:edge_num(), %Right traversal predecessor
	 rtsu=0	:: wings_edge:edge_num()  %Right traversal successor
	}).

%% Display lists per object.
%%  Important: Plain integers and integers in lists will be assumed to
%%  be display lists. Arbitrary integers must be stored inside a tuple
%%  or record to not be interpreted as a display list.
-record(dlo,
        {work=none :: wings_dl:dl(),            %Workmode faces.
         smooth=none :: wings_dl:dl(),          %Smooth-shaded faces.
         edges=none :: wings_dl:dl(),           %Edges and wire-frame.
         vs=none :: wings_dl:dl(),              %Unselected vertices.
         hard=none :: wings_dl:dl(),            %Hard edges.
         sel=none :: wings_dl:sel_dl(),         %Selected items.
         orig_sel=none :: wings_dl:sel_dl(),    %Original selection.
         normals=none :: wings_dl:dl(),         %Normals.

         vab=none :: 'none' | vab(),            %Vertex array (see below)
         tri_map=none :: 'none' | wings_pick:tri_map(), %Tri -> Face map (for picking)

	 %% Miscellanous.
         hilite=none ::
           'none' | {wings_sel:mode(),wings_dl:dl()},  %Hilite display list.
         mirror=none ::
           'none' | e3d_mat:matrix(),           %Virtual mirror data.
         ns=none :: wings_draw:normals(),       %Normals/positions per face.
	 plugins=[],                            %Draw lists for plugins.

         %% Proxy stuff.
         proxy=false :: boolean(),              %Proxy Data is used.
         proxy_data=none ::
           'none' | wings_proxy:sp(),           %Data for smooth proxy.

	 %% Source for display lists.
         src_we=none :: 'none' | #we{},         %Source object.
         src_sel=none :: 'none' |
                         {wings_sel:mode(),wings_sel:item_set()}, %Source selection.
         split=none ::
           'none' | wings_draw:split(),         %Split data.
         drag=none :: 'none'
                    | wings_drag:drag()
                    | wings_tweak:drag()
                    | {matrix,_,_,e3d_mat:matrix()}, %For dragging.
         transparent=false :: boolean() | #we{}, %Object includes transparancy.
         open=false :: boolean(),               %Open (has hole).

	 %% List of display lists known to be needed only based
	 %% on display modes, not whether the lists themselves exist.
	 %% Example: [work,edges]
         needed=[] :: [atom()]
	}).

%% Vertex Buffer Objects. The name is #vab{} for historical reasons.
-record(vab, 
	{
	  id :: non_neg_integer(), %Unique identifier for this instance.
	  data,			 %Copy of data in VBO (for picking).

	  %% Vertex buffers. Each vertex buffer looks like
	  %% {Stride,Binary}, where Stride is the stride to be
	  %% used when setting up the vertex buffer.
	  face_vs  = none :: wings_vtx_buffer(), %Vertex binary for drawing faces
	  face_fn  = none :: wings_vtx_buffer(), %Face Normals (flat but per vertex)
	  face_sn  = none ::			%Face Normals (smooth)
	    {'vbo',non_neg_integer()} | wings_vtx_buffer(),
	  face_uv  = none :: wings_vtx_buffer(), %UV coords
	  face_ts  = none :: wings_vtx_buffer(), %Tangent vector
	  face_vc  = none :: wings_vtx_buffer(), %Vertex Colors coords
	  face_es  = none ::
            {0, binary()} | wings_vtx_buffer(),  %Edges 2*Vertex coords
	  face_map = none ::
            'none' | wings_draw_setup:face_map(), %FaceId -> {BinPos,TriCount}
	  mat_map  = none                        %Face per Material draw info
	 }).

-type vab() :: #vab{}.

