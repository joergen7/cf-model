%% -*- erlang -*-

-module( sem_test ).
-author( "Jorgen Brandt <brandjoe@hu-berlin.de>" ).

-include_lib( "eunit/include/eunit.hrl" ).


-define( THETA0, {#{}, fun sem:mu/1, #{}, #{}} ).





%% =============================================================================
%% Predicates
%% =============================================================================

%% Finality %%

str_should_be_final_test() ->
  S = {str, "blub"},
  ?assert( sem:pfinal( S ) ).

app_should_not_be_final_test() ->
  A = {app, 1, {var, "f"}, #{}},
  ?assertNot( sem:pfinal( A ) ).

cnd_should_not_be_final_test() ->
  C = {cnd, [{str, "a"}], [{str, "b"}], [{str, "c"}]},
  ?assertNot( sem:pfinal( C ) ).

select_should_not_be_final_test() ->
  Fut = {fut, 1234, [{param, "out", false}]},
  S = {select, 1, Fut},
  ?assertNot( sem:pfinal( S ) ).

var_should_not_be_final_test() ->
  V = {var, "x"},
  ?assertNot( sem:pfinal( V ) ).

all_str_should_be_final_test() ->
  X = [{str, "bla"}, {str, "blub"}],
  ?assert( sem:pfinal( X ) ).

empty_lst_should_be_final_test() ->
  ?assert( sem:pfinal( [] ) ).

one_var_lst_should_not_be_final_test() ->
  X = [{str, "bla"}, {str, "blub"}, {var, "x"}],
  ?assertNot( sem:pfinal( X ) ).

all_var_lst_should_not_be_final_test() ->
  X = [{var, "bla"}, {var, "blub"}, {var, "x"}],
  ?assertNot( sem:pfinal( X ) ).

empty_map_should_be_final_test() ->
  ?assert( sem:pfinal( #{} ) ).

only_str_map_should_be_final_test() ->
  M = #{"x" => [{str, "bla"}, {str, "blub"}], "y" => [{str, "shalala"}]},
  ?assert( sem:pfinal( M ) ).

one_var_map_should_not_be_final_test() ->
  M = #{"x" => [{str, "bla"}, {str, "blub"}],
        "y" => [{str, "shalala"}, {var, "x"}]},
  ?assertNot( sem:pfinal( M ) ).

all_var_map_should_not_be_final_test() ->
  M = #{"x" => [{var, "bla"}, {var, "blub"}],
        "y" => [{var, "shalala"}, {var, "x"}]},
  ?assertNot( sem:pfinal( M ) ).

%% Singularity %%

app_without_arg_should_be_singular_test() ->
  S = {sign, [{param, "out", false}], []},
  B = {forbody, bash, "shalala"},
  Lam = {lam, S, B},
  App = {app, 1, Lam, #{}},
  ?assert( sem:psing( App ) ).

app_binding_single_str_should_be_singular_test() ->
  S = {sign, [{param, "out", false}], [{param, "x", false}]},
  B = {forbody, bash, "shalala"},
  Lam = {lam, S, B},
  App = {app, 1, Lam, #{"x" => [{str, "bla"}]}},
  ?assert( sem:psing( App ) ).

app_binding_str_lst_should_not_be_singular_test() ->
  S = {sign, [{param, "out", false}], [{param, "x", false}]},
  B = {forbody, bash, "shalala"},
  Lam = {lam, S, B},
  App = {app, 1, Lam, #{"x" => [{str, "bla"}, {str, "blub"}]}},
  ?assertNot( sem:psing( App ) ).

app_with_only_aggregate_args_should_be_singular_test() ->
  S = {sign, [{param, "out", false}], [{param, "x", true}]},
  B = {forbody, bash, "shalala"},
  Lam = {lam, S, B},
  App = {app, 1, Lam, #{"x" => [{str, "bla"}, {str, "blub"}]}},
  ?assert( sem:psing( App ) ).

%% Enumerability %%

empty_lst_should_be_enumerable_test() ->
  ?assert( sem:pen( [] ) ).

str_lst_should_be_enumerable_test() ->
  ?assert( sem:pen( [{str, "a"}, {str, "b"}] ) ).

one_var_lst_should_not_be_enumerable_test() ->
  ?assertNot( sem:pen( [{str, "a"}, {var, "x"}] ) ).

all_var_lst_should_not_be_enumerable_test() ->
  ?assertNot( sem:pen( [{var, "x"}, {var, "y"}] ) ).

str_should_be_enumerable_test() ->
  ?assert( sem:pen( {str, "blub"} ) ).

single_str_branch_cnd_should_be_enumerable_test() ->
  ?assert( sem:pen( {cnd, [], [{str, "a"}], [{str, "b"}]} ) ).

empty_then_branch_cnd_should_not_be_enumerable_test() ->
  ?assertNot( sem:pen( {cnd, [], [], [{str, "b"}]} ) ).

empty_else_branch_cnd_should_not_be_enumerable_test() ->
  ?assertNot( sem:pen( {cnd, [], [{str, "a"}]} ) ).

select_non_lst_app_should_be_enumerable_test() ->
  Sign = {sign, [{param, "out", false}], []},
  Body = {forbody, bash, "shalala"},
  Lam = {lam, Sign, Body},
  App = {app, 1, Lam, #{}},
  ?assert( sem:pen( App ) ).

select_lst_app_should_not_be_enumerable_test() ->
  Sign = {sign, [{param, "out", true}], []},
  Body = {forbody, bash, "shalala"},
  Lam = {lam, Sign, Body},
  App = {app, 1, Lam, #{}},
  ?assertNot( sem:pen( App ) ).

non_singular_app_should_not_be_enumerable_test() ->
  Sign = {sign, [{param, "out", false}], [{param, "x", false}]},
  Body = {forbody, bash, "shalala"},
  Lam = {lam, Sign, Body},
  Fa = #{"x" => [{str, "bla"}, {str, "blub"}]},
  App = {app, 1, Lam, Fa},
  ?assertNot( sem:pen( App ) ).

non_lst_select_should_be_enumerable_test() ->
  Lo = [{param, "out", false}],
  Fut = {fut, 1234, Lo},
  Select = {select, 1, Fut},
  ?assert( sem:pen( Select ) ).

lst_select_should_not_be_enumerable_test() ->
  Lo = [{param, "out", true}],
  Fut = {fut, 1234, Lo},
  Select = {select, 1, Fut},
  ?assertNot( sem:pen( Select ) ).

  
%% =============================================================================
%% Evaluation
%% =============================================================================

nil_should_eval_itself_test() ->
  ?assertEqual( [], sem:eval( [], ?THETA0 ) ).

str_should_eval_itself_test() ->
  E = [{str, "bla"}],
  ?assertEqual( E, sem:eval( E, ?THETA0 ) ).

undef_var_should_fail_test() ->
  E = [{var, "x"}],
  ?assertError( {badkey, "x"}, sem:eval( E, ?THETA0 ) ).

def_var_should_eval_to_bound_value_test() ->
  E = [{str, "blub"}],
  X = sem:eval( [{var, "x"}], {#{"x" => E}, fun sem:mu/1, #{}, #{}} ),
  ?assertEqual( E, X ).

def_var_should_cascade_binding_test() ->
  E = [{str, "blub"}],
  Theta = {#{"x" => [{var, "y"}], "y" => E}, fun sem:mu/1, #{}, #{}},
  X = sem:eval( [{var, "x"}], Theta ),
  ?assertEqual( E, X ).

def_var_should_cascade_binding_twice_test() ->
  A = [{str, "A"}],
  Rho = #{"x" => [{var, "y"}], "y" => [{var, "z"}], "z" => A},
  ?assertEqual( A, sem:eval( [{var, "x"}], {Rho, fun sem:mu/1, #{}, #{}} ) ).

unfinished_select_should_eval_to_itself_test() ->
  Fut = {fut, 1234, [{param, "out", false}]},
  E = [{select, 1, Fut}],
  X = sem:eval( E, ?THETA0 ),
  ?assertEqual( E, X ).
  
finished_select_should_eval_to_result_test() ->
  Fut = {fut, 1234, [{param, "out", false}]},
  S = {select, 1, Fut},
  F = [{str, "blub"}],
  Theta = {#{}, fun sem:mu/1, #{}, #{{"out", 1234} => F}},
  X = sem:eval( [S], Theta ),
  ?assertEqual( F, X ).

noarg_fn_should_eval_plain_test() ->
  E = [{str, "bla"}],
  Sign = {sign, [{param, "out", false}], []},
  Body = {natbody, #{"out" => E}},
  Lam = {lam, Sign, Body},
  F = [{app, 1, Lam, #{}}],
  ?assertEqual( E, sem:eval( F, ?THETA0 ) ).
  
noarg_fn_should_eval_body_test() ->
  E = [{str, "bla"}],
  Sign = {sign, [{param, "out", false}], []},
  Body = {natbody, #{"out" => [{var, "x"}], "x" => E}},
  Lam = {lam, Sign, Body},
  F = [{app, 1, Lam, #{}}],
  ?assertEqual( E, sem:eval( F, ?THETA0 ) ).
  
fn_call_should_insert_lam_test() ->
  E = [{str, "bla"}],
  Sign = {sign, [{param, "out", false}], []},
  Body = {natbody, #{"out" => E}},
  Lam = {lam, Sign, Body},
  F = [{app, 1, {var, "f"}, #{}}],
  Theta = {#{}, fun sem:mu/1, #{"f" => Lam}, #{}},
  ?assertEqual( E, sem:eval( F, Theta ) ).
  
app_with_unbound_lam_should_fail_test() ->
  F = [{app, 1, {var, "f"}, #{}}],
  ?assertError( {badkey, "f"}, sem:eval( F, ?THETA0 ) ).

identity_fn_should_eval_arg_test() ->
  E = [{str, "bla"}],
  Sign = {sign, [{param, "out", false}], [{param, "inp", false}]},
  Body = {natbody, #{"out" => [{var, "inp"}]}},
  Lam = {lam, Sign, Body},
  F = [{app, 1, Lam, #{"inp" => E}}],
  ?assertEqual( E, sem:eval( F, ?THETA0 ) ).

multiple_output_should_be_bindable_test() ->
  Sign = {sign, [{param, "out1", false}, {param, "out2", false}], []},
  E1 = [{str, "bla"}],
  E2 = [{str, "blub"}],
  Body = {natbody, #{"out1" => E1, "out2" => E2}},
  Lam = {lam, Sign, Body},
  F1 = [{app, 1, Lam, #{}}],
  F2 = [{app, 2, Lam, #{}}],
  [?assertEqual( E1, sem:eval( F1, ?THETA0 ) ),
   ?assertEqual( E2, sem:eval( F2, ?THETA0 ) )].
   
app_should_ignore_calling_context_test() ->
  Sign = {sign, [{param, "out", false}], []},
  Body = {natbody, #{"out" => [{var, "x"}]}},
  Lam = {lam, Sign, Body},
  X = [{app, 1, Lam, #{}}],
  Rho = #{"x" => [{str, "blub"}]},
  ?assertError( {badkey, "x"}, sem:eval( X, {Rho, fun sem:mu/1, #{}, #{}} ) ).

app_should_hand_down_gamma_test() ->
  Sign = {sign, [{param, "out", false}], []},
  Body = {natbody, #{"out" => [{app, 1, {var, "f"}, #{}}]}},
  Lam = {lam, Sign, Body},
  X = [{app, 1, Lam, #{}}],
  E = [{str, "blub"}],
  Gamma = #{"f" => {lam, Sign, {natbody, #{"out" => E}}}},
  Theta = {#{}, fun sem:mu/1, Gamma, #{}},
  ?assertEqual( E, sem:eval( X, Theta ) ).
  
binding_should_override_body_test() ->
  F = [{str, "blub"}],
  Sign = {sign, [{param, "out", false}], [{param, "x", false}]},
  Body = {natbody, #{"x" => [{str, "bla"}], "out" => [{var, "x"}]}},
  Lam = {lam, Sign, Body},
  X = [{app, 1, Lam, #{"x" => F}}],
  ?assertEqual( F, sem:eval( X, ?THETA0 ) ).
  
returning_empty_list_on_nonlist_output_channel_should_fail_test() ->
  S = {sign, [{param, "out", false}], []},
  B = {natbody, #{"out" => []}},
  Lam = {lam, S, B},
  X = [{app, 1, Lam, #{}}],
  ?assertError( output_sign_mismatch, sem:eval( X, ?THETA0 ) ).

cross_product_should_be_derivable_test() ->
  Sign = {sign, [{param, "out1", false}, {param, "out2", false}],
                [{param, "p1", false}, {param, "p2", false}]},
  E1 = [{str, "A"}, {str, "B"}],
  E2 = [{str, "1"}, {str, "2"}],
  Body = {natbody, #{"out1" => [{var, "p1"}], "out2" => [{var, "p2"}]}},
  Lam = {lam, Sign, Body},
  Binding = #{"p1" => E1, "p2" => E2},
  App1 = [{app, 1, Lam, Binding}],
  App2 = [{app, 2, Lam, Binding}],
  F1 = [{str, "A"}, {str, "A"}, {str, "B"}, {str, "B"}],
  F2 = [{str, "1"}, {str, "2"}, {str, "1"}, {str, "2"}],
  [?assertEqual( F1, sem:eval( App1, ?THETA0 ) ),
   ?assertEqual( F2, sem:eval( App2, ?THETA0 ) )].

dot_product_should_be_derivable1_test() ->
  Sign = {sign, [{param, "out1", false}, {param, "out2", false}],
                [{correl, ["p1", "p2"]}]},
  E1 = [{str, "A"}],
  E2 = [{str, "1"}],
  Body = {natbody, #{"out1" => [{var, "p1"}], "out2" => [{var, "p2"}]}},
  Lam = {lam, Sign, Body},
  Binding = #{"p1" => E1, "p2" => E2},
  App1 = [{app, 1, Lam, Binding}],
  App2 = [{app, 2, Lam, Binding}],
  [?assertEqual( E1, sem:eval( App1, ?THETA0 ) ),
   ?assertEqual( E2, sem:eval( App2, ?THETA0 ) )].

dot_product_should_be_derivable2_test() ->
  Sign = {sign, [{param, "out1", false}, {param, "out2", false}],
                [{correl, ["p1", "p2"]}]},
  E1 = [{str, "A"}, {str, "B"}],
  E2 = [{str, "1"}, {str, "2"}],
  Body = {natbody, #{"out1" => [{var, "p1"}], "out2" => [{var, "p2"}]}},
  Lam = {lam, Sign, Body},
  Binding = #{"p1" => E1, "p2" => E2},
  App1 = [{app, 1, Lam, Binding}],
  App2 = [{app, 2, Lam, Binding}],
  [?assertEqual( E1, sem:eval( App1, ?THETA0 ) ),
   ?assertEqual( E2, sem:eval( App2, ?THETA0 ) )].

dot_product_should_be_derivable3_test() ->
  Sign = {sign, [{param, "out1", false}, {param, "out2", false}],
                [{correl, ["p1", "p2"]}]},
  E1 = [{str, "A"}, {str, "B"}, {str, "C"}],
  E2 = [{str, "1"}, {str, "2"}, {str, "3"}],
  Body = {natbody, #{"out1" => [{var, "p1"}], "out2" => [{var, "p2"}]}},
  Lam = {lam, Sign, Body},
  Binding = #{"p1" => E1, "p2" => E2},
  App1 = [{app, 1, Lam, Binding}],
  App2 = [{app, 2, Lam, Binding}],
  [?assertEqual( E1, sem:eval( App1, ?THETA0 ) ),
   ?assertEqual( E2, sem:eval( App2, ?THETA0 ) )].
   
aggregate_should_consume_whole_list_test() ->
  Sign = {sign, [{param, "out", true}],
                [{param, "inp", true}]},
  E1 = [{str, "A"}],
  E2 = [{str, "B"}, {str, "C"}],
  Body = {natbody, #{"out" => E1++[{var, "inp"}]}},
  Lam = {lam, Sign, Body},
  Binding = #{"inp" => E2},
  App = [{app, 1, Lam, Binding}],
  ?assertEqual( E1++E2, sem:eval( App, ?THETA0 ) ).

cnd_false_should_eval_else_expr_test() ->
  E = [{cnd, [], [{str, "A"}], [{str, "B"}]}],
  ?assertEqual( [{str, "B"}], sem:eval( E, ?THETA0 ) ).
  
cnd_evaluates_condition_before_decision1_test() ->
  Sign = {sign, [{param, "out", true}], []},
  Body = {natbody, #{"out" => []}},
  Lam = {lam, Sign, Body},
  App = [{app, 1, Lam, #{}}],
  E = [{cnd, App, [{str, "A"}], [{str, "B"}]}],
  ?assertEqual( [{str, "B"}], sem:eval( E, ?THETA0 ) ).

cnd_evaluates_condition_before_decision2_test() ->
  Sign = {sign, [{param, "out", true}], []},
  Body = {natbody, #{"out" => [{str, "X"}]}},
  Lam = {lam, Sign, Body},
  App = [{app, 1, Lam, #{}}],
  E = [{cnd, App, [{str, "A"}], [{str, "B"}]}],
  ?assertEqual( [{str, "A"}], sem:eval( E, ?THETA0 ) ).
  
cnd_evaluates_only_on_final_condition_test() ->
  Sign = {sign, [{param, "out", true}], []},
  Lam = {lam, Sign, {forbody, bash, "shalala"}},
  App = [{app, 1, Lam, #{}}],
  A = [{var, "a"}],
  B = [{var, "b"}],
  E = [{cnd, App, A, B}],
  Rho = #{"a" => [{str, "A"}], "b" => [{str, "B"}]},
  X = sem:eval( E, {Rho, fun sem:mu/1, #{}, #{}} ),
  ?assertMatch( [{cnd, [{select, _, _}], A, B}], X ).

cnd_evaluates_then_expr_test() ->
  E = [{cnd, [{str, "Z"}], [{var, "x"}], [{str, "B"}]}],
  F = [{str, "A"}],
  Theta = {#{"x" => F}, fun sem:mu/1, #{}, #{}},
  ?assertEqual( F, sem:eval( E, Theta ) ).
  
cnd_evaluates_else_expr_test() ->
  E = [{cnd, [], [{str, "B"}], [{var, "x"}]}],
  F = [{str, "A"}],
  Theta = {#{"x" => F}, fun sem:mu/1, #{}, #{}},
  ?assertEqual( F, sem:eval( E, Theta ) ).

foreign_app_with_cnd_param_is_left_untouched_test() ->
  Sign = {sign, [{param, "out", false}], [{param, "p", false}]},
  Lam = {lam, Sign, {forbody, bash, "shalala"}},
  App1 = [{app, 1, Lam, #{"p" => [{str, "A"}]}}],
  E = [{cnd, App1, [], []}],
  App2 = [{app, 1, Lam, #{"p" => E}}],
  X = sem:eval( App2, ?THETA0 ),
  ?assertMatch( [{app, 1, Lam, _}], X ).
  
foreign_app_with_select_param_is_left_untouched_test() ->
  Sign = {sign, [{param, "out", false}],
                [{param, "p", false}]},
  Lam = {lam, Sign, {forbody, bash, "shalala"}},
  App1 = [{app, 1, Lam, #{"p" => [{str, "A"}]}}],
  App2 = [{app, 1, Lam, #{"p" => App1}}],
  X = sem:eval( App2, ?THETA0 ),
  ?assertMatch( [{app, 1, Lam, _}], X ).
  
app_non_final_result_preserves_app_test() ->
  Sign = {sign, [{param, "out", false}], []},
  Body = {natbody, #{"out" => [{cnd, [{select, 1, {fut, 1234, [{param, "out", false}]}}], [{var, "x"}], [{var, "y"}]}]}},
  Lam = {lam, Sign, Body},
  App = [{app, 1, Lam, #{}}],
  X = sem:eval( App, ?THETA0 ),
  ?assertMatch( App, X ).

app_tail_recursion_is_optimized_test() ->
  Sign = {sign, [{param, "out", false}], []},
  Select = [{select, 1, {fut, 1234, [{param, "out", false}]}}],
  Body = {natbody, #{"out" => Select}},
  Lam = {lam, Sign, Body},
  App = [{app, 1, Lam, #{}}],
  X = sem:eval( App, ?THETA0 ),
  ?assertMatch( Select, X ).


app_non_final_result_preserves_app_with_new_lam_test() ->
  CSign = {sign, [{param, "out", true}], []},
  CLam = {lam, CSign, {forbody, bash, "shalala"}},
  CApp = [{app, 1, CLam, #{}}],
  Sign = {sign, [{param, "out", false}], []},
  Body = {natbody, #{"out" => [{cnd, CApp, [{var, "x"}], [{var, "x"}]}],
                     "x" => [{str, "A"}]}},
  Lam = {lam, Sign, Body},
  App = [{app, 1, Lam, #{}}],
  X = sem:eval( App, ?THETA0 ),
  [{app, 1, {lam, Sign, {natbody, BodyMap1}}, #{}}] = X,
  Val = maps:get( "out", BodyMap1 ),
  ?assertMatch( [{cnd, [{select, 1, _}], [{var, "x"}], [{var, "x"}]}], Val ).

nested_app_undergoes_reduction_test() ->
  Sign = {sign, [{param, "out", false}], []},
  Lam1 = {lam, Sign, {forbody, bash, "shalala"}},
  App1 = [{app, 1, Lam1, #{}}],
  Body2 = {natbody, #{"out" => App1}},
  Lam2 = {lam, Sign, Body2},
  App2 = [{app, 1, Lam2, #{}}],
  X = sem:eval( App2, ?THETA0 ),
  [{select, 1, {fut, R, _}}] = X,
  Omega = #{{"out", R} => [{str, "A"}]},
  Y = sem:eval( X, {#{}, fun sem:mu/1, #{}, Omega} ),
  ?assertEqual( [{str, "A"}], Y ).

app_select_param_is_enumerated_test() ->
  Sign1 = {sign, [{param, "out", false}], []},
  Lam1 = {lam, Sign1, {forbody, bash, "shalala"}},
  Sign2 = {sign, [{param, "out", false}],
                 [{param, "inp", false}]},
  Body2 = {natbody, #{"out" => [{var, "inp"}]}},
  Lam2 = {lam, Sign2, Body2},
  A0 = {app, 1, Lam1, #{}},
  A = [A0, A0],
  B = [{app, 1, Lam2, #{"inp" => A}}],
  X = sem:eval( B, ?THETA0 ), 
  ?assertMatch( [{select, 1, _}, {select, 1, _}], X ).



% deftask find_clusters( cls( File ) : state( File ) ) {
%   cls = state;
% }
% mu0 = 1;
% cls = find_clusters( state: mu0 );
% cls;
identity_fn_should_resolve_var_test() ->
  Lo = [{param, "cls", false}],
  Li = [{param, "state", false}],
  Sign = {sign, Lo, Li},
  Body = {natbody, #{"cls" => [{var, "state"}]}},
  Lam = {lam, Sign, Body},
  Fa = #{"state" => [{var, "mu0"}]},
  App = {app, 1, Lam, Fa},
  Rho = #{"cls" => [App], "mu0" => [{str, "1"}]},
  X = [{var, "cls"}],
  ?assertEqual( [{str, "1"}], sem:eval( X, {Rho, fun sem:mu/1, #{}, #{}} ) ).


%% =============================================================================
%% Enumeration
%% =============================================================================

%% The enum Function %%

enum_app_without_app_does_nothing_test() ->
  S = {sign, [{param, "out", false}], []},
  B = {forbody, bash, "shalala"},
  Lam = {lam, S, B},
  App = {app, 1, Lam, #{}},
  ?assertEqual( [App], sem:enum_app( App ) ).

%% Enumeration Rules %%

%% Augmentation %%

can_aug_argpair_with_param_test() ->
  L0 = [{param, "b", false}, {param, "c", false}],
  F = #{"a" => [{str, "1"}], "b" => [{str, "2"}], "c" => [{str, "3"}]},
  Pair = {L0, F},
  I = {param, "a", false},
  L1 = [I|L0],
  ?assertEqual( {L1, F}, sem:aug_argpair( Pair, I ) ).

can_aug_argpair_with_correl_test() ->
  L0 = [{param, "b", false}, {param, "c", false}],
  F = #{"a1" => [{str, "11"}],
        "a2" => [{str, "12"}],
        "b" => [{str, "2"}],
        "c" => [{str, "3"}]},
  Pair = {L0, F},
  I = {correl, ["a1", "a2"]},
  L1 = [{param, "a1", false}, {param, "a2", false}|L0],
  ?assertEqual( {L1, F}, sem:aug_argpair( Pair, I ) ).

can_augment_empty_argpairlist_with_param_test() ->
  F1 = #{"a" => [{str, "x1"}]},
  F2 = #{"a" => [{str, "y1"}]},
  PairList = [{[], F1}, {[], F2}],
  I = {param, "a", false},
  L1 = [{param, "a", false}],
  ?assertEqual( [{L1, F1}, {L1, F2}], sem:aug( PairList, I ) ).

can_augment_argpairlist_with_param_test() ->
  L0 = [{param, "b", false}, {param, "c", false}],
  F1 = #{"a" => [{str, "x1"}], "b" => [{str, "x2"}], "c" => [{str, "x3"}]},
  F2 = #{"a" => [{str, "y1"}], "b" => [{str, "y2"}], "c" => [{str, "y3"}]},
  PairList = [{L0, F1}, {L0, F2}],
  I = {param, "a", false},
  L1 = [{param, "a", false}|L0],
  ?assertEqual( [{L1, F1}, {L1, F2}], sem:aug( PairList, I ) ).

can_augment_argpairlist_with_correl_test() ->
  L0 = [{param, "b", false}, {param, "c", false}],
  F1 = #{"a1" => [{str, "x11"}],
         "a2" => [{str, "x12"}],
         "b" => [{str, "x2"}],
         "c" => [{str, "x3"}]},
  F2 = #{"a1" => [{str, "y11"}],
         "a2" => [{str, "y12"}],
         "b" => [{str, "y2"}],
         "c" => [{str, "y3"}]},
  PairList = [{L0, F1}, {L0, F2}],
  I = {correl, ["a1", "a2"]},
  L1 = [{param, "a1", false}, {param, "a2", false}|L0],
  ?assertEqual( [{L1, F1}, {L1, F2}], sem:aug( PairList, I ) ).

%% Correlation %%

corrstep_should_separate_first_value_single_test() ->
  Lc = ["a"],
  F0 = #{"a" => [{str, "1"}, {str, "2"}, {str, "3"}]},
  Y = {#{"a" => [{str, "1"}]}, #{"a" => [{str, "2"}, {str, "3"}]}},
  X = sem:corrstep( Lc, F0, F0 ),
  ?assertEqual( Y, X ).

corrstep_should_separate_first_value_two_test() ->
  Lc = ["a", "b"],
  F0 = #{"a" => [{str, "1"}, {str, "2"}, {str, "3"}], "b" => [{str, "A"}, {str, "B"}, {str, "C"}]},
  Y = {#{"a" => [{str, "1"}], "b" => [{str, "A"}]}, #{"a" => [{str, "2"}, {str, "3"}], "b" => [{str, "B"}, {str, "C"}]}},
  X = sem:corrstep( Lc, F0, F0 ),
  ?assertEqual( Y, X ).
