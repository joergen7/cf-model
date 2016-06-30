%% -*- erlang -*-

-module( sem_test ).
-author( "Jorgen Brandt <brandjoe@hu-berlin.de>" ).

-include_lib( "eunit/include/eunit.hrl" ).


-define( THETA0, {#{}, fun sem:mu/1, #{}, #{}} ).





%% =============================================================================
%% Predicates
%% =============================================================================

%% Normal Form %%

str_should_be_in_normal_test() ->
  S = {str, "blub"},
  ?assert( sem:pnormal( S ) ).

app_should_not_be_normal_test() ->
  A = {app, 1, {var, "f"}, #{}},
  ?assertNot( sem:pnormal( A ) ).

cnd_should_not_be_normal_test() ->
  C = {cnd, [{str, "a"}], [{str, "b"}], [{str, "c"}]},
  ?assertNot( sem:pnormal( C ) ).

select_should_not_be_normal_test() ->
  Fut = {fut, 1234, [{param, "out", false}]},
  S = {select, 1, Fut},
  ?assertNot( sem:pnormal( S ) ).

var_should_not_be_normal_test() ->
  V = {var, "x"},
  ?assertNot( sem:pnormal( V ) ).

all_str_should_be_normal_test() ->
  X = [{str, "bla"}, {str, "blub"}],
  ?assert( sem:pnormal( X ) ).

empty_lst_should_be_normal_test() ->
  ?assert( sem:pnormal( [] ) ).

one_var_lst_should_not_be_normal_test() ->
  X = [{str, "bla"}, {str, "blub"}, {var, "x"}],
  ?assertNot( sem:pnormal( X ) ).

all_var_lst_should_not_be_normal_test() ->
  X = [{var, "bla"}, {var, "blub"}, {var, "x"}],
  ?assertNot( sem:pnormal( X ) ).

empty_map_should_be_normal_test() ->
  ?assert( sem:pnormal( #{} ) ).

only_str_map_should_be_normal_test() ->
  M = #{"x" => [{str, "bla"}, {str, "blub"}], "y" => [{str, "shalala"}]},
  ?assert( sem:pnormal( M ) ).

one_var_map_should_not_be_normal_test() ->
  M = #{"x" => [{str, "bla"}, {str, "blub"}],
        "y" => [{str, "shalala"}, {var, "x"}]},
  ?assertNot( sem:pnormal( M ) ).

all_var_map_should_not_be_normal_test() ->
  M = #{"x" => [{var, "bla"}, {var, "blub"}],
        "y" => [{var, "shalala"}, {var, "x"}]},
  ?assertNot( sem:pnormal( M ) ).

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

app_str_is_evaluated_while_select_remains_test() ->
  Sign2 = {sign, [{param, "out", false}],
                 [{param, "inp", false}]},
  Body2 = {forbody, bash, "lalala"},
  Lam2 = {lam, Sign2, Body2},
  Fut = {fut, 1234, [{param, "y", false}]},
  Select = {select, 1, Fut},
  Str = {str, "blub"},
  A = [Str, Select],
  B = [{app, 1, Lam2, #{"inp" => A}}],
  X = sem:eval( B, ?THETA0 ), 
  ?assertMatch( [{select, 1, {fut, _, [{param, "out", false}]}},
                 {app, 1, Lam2, #{"inp" := [Select]}}], X ).

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

enum_without_app_does_nothing_test() ->
  S = {sign, [{param, "out", false}], []},
  B = {forbody, bash, "shalala"},
  Lam = {lam, S, B},
  App = {app, 1, Lam, #{}},
  ?assertEqual( [App], sem:enum( App ) ).

%% Enumeration Rules %%

%% Augmentation %%

can_aug_with_param_test() ->
  Lo = [{param, "out", false}],
  B = {forbody, bash, "blub"},
  L0 = [{param, "b", false}, {param, "c", false}],
  F = #{"a" => [{str, "1"}], "b" => [{str, "2"}], "c" => [{str, "3"}]},
  App = {app, 1, {lam, {sign, Lo, L0}, B}, F},
  I = {param, "a", false},
  L1 = [I|L0],
  ?assertEqual( {app, 1, {lam, {sign, Lo, L1}, B}, F}, sem:aug( App, I ) ).

can_aug_with_correl_test() ->
  Lo = [{param, "out", false}],
  B = {forbody, bash, "blub"},
  L0 = [{param, "b", false}, {param, "c", false}],
  F = #{"a1" => [{str, "11"}],
        "a2" => [{str, "12"}],
        "b" => [{str, "2"}],
        "c" => [{str, "3"}]},
  App = {app, 1, {lam, {sign, Lo, L0}, B}, F},
  I = {correl, ["a1", "a2"]},
  L1 = [{param, "a1", false}, {param, "a2", false}|L0],
  ?assertEqual( {app, 1, {lam, {sign, Lo, L1}, B}, F}, sem:aug( App, I ) ).

can_augment_empty_inparamlst_with_param_test() ->
  Lo = [{param, "out", false}],
  B = {forbody, bash, "blub"},
  F1 = #{"a" => [{str, "x1"}]},
  F2 = #{"a" => [{str, "y1"}]},
  PairList = [{app, 1, {lam, {sign, Lo, []}, B}, F1},
              {app, 1, {lam, {sign, Lo, []}, B}, F2}],
  I = {param, "a", false},
  L1 = [{param, "a", false}],
  X = [{app, 1, {lam, {sign, Lo, L1}, B}, F1},
       {app, 1, {lam, {sign, Lo, L1}, B}, F2}],
  ?assertEqual( X, sem:aug_lst( PairList, I ) ).

can_augment_inparamlst_with_param_test() ->
  Lo = [{param, "out", false}],
  B = {forbody, bash, "blub"},
  L0 = [{param, "b", false}, {param, "c", false}],
  F1 = #{"a" => [{str, "x1"}], "b" => [{str, "x2"}], "c" => [{str, "x3"}]},
  F2 = #{"a" => [{str, "y1"}], "b" => [{str, "y2"}], "c" => [{str, "y3"}]},
  AppList = [{app, 1, {lam, {sign, Lo, L0}, B}, F1},
             {app, 1, {lam, {sign, Lo, L0}, B}, F2}],
  I = {param, "a", false},
  L1 = [{param, "a", false}|L0],
  X = [{app, 1, {lam, {sign, Lo, L1}, B}, F1},
       {app, 1, {lam, {sign, Lo, L1}, B}, F2}],
  ?assertEqual( X, sem:aug_lst( AppList, I ) ).

can_augment_inparamlst_with_correl_test() ->
  Lo = [{param, "out", false}],
  B = {forbody, bash, "blub"},
  L0 = [{param, "b", false}, {param, "c", false}],
  F1 = #{"a1" => [{str, "x11"}],
         "a2" => [{str, "x12"}],
         "b" => [{str, "x2"}],
         "c" => [{str, "x3"}]},
  F2 = #{"a1" => [{str, "y11"}],
         "a2" => [{str, "y12"}],
         "b" => [{str, "y2"}],
         "c" => [{str, "y3"}]},
  AppList = [{app, 1, {lam, {sign, Lo, L0}, B}, F1},
             {app, 1, {lam, {sign, Lo, L0}, B}, F2}],
  I = {correl, ["a1", "a2"]},
  L1 = [{param, "a1", false}, {param, "a2", false}|L0],
  X = [{app, 1, {lam, {sign, Lo, L1}, B}, F1},
       {app, 1, {lam, {sign, Lo, L1}, B}, F2}],
  ?assertEqual( X, sem:aug_lst( AppList, I ) ).

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



% deftask bwa-mem( outbam( File ) : fastq( File ) )in bash *{
%   ...
% }*
%
% deftask compareToCTRL( somaticVCF( File ) : <tumorParts( False )> ctrlBam( File ) ) in bash *{
%   ...
% }*
%
% deftask getVariants( somaticVCF( File ) : tumor( File ), <ctrlBam( File )> ) {
% 
%   tumorBam   = bwa-mem( fastq: tumor );
%   somaticVCF = compareToCTRL( ctrlBam: ctrlBam, tumorParts: tumorBam );
% }
%
% ctrlFq = "ctrl.fq"
% tumorFq = "tumor.fq"
%
% ctrlBam    = bwa-mem( fastq: ctrlFq );
% somaticVCF = getVariants( ctrlBam: ctrlBam, tumor: tumorFq );
%
% somaticVCF;

christopher_test() ->
  X = [{app,1,
              {lam,{sign,[{param,"somaticVCF",false}],
                         [{param,"tumor",false},
                          {param,"ctrlBam",true}]},
                   {natbody,#{"somaticVCF" => [{app,1,
                                    {var,"compareToCTRL"},
                                    #{"ctrlBam"    => [{var,"ctrlBam"}],
                                      "tumorParts" => [{var,"tumorBam"}]}}],
                              "tumorBam" => [{app,1,
                                    {var,"bwa-mem"},
                                    #{"fastq" => [{var,"tumor"}]}}]}}},
              #{"ctrlBam" => [{select,1,{fut,1,[{param,"bamout",false}]}}],
                "tumor" => [{str,"data/CH_JK_001/CH_JK_001_R1_001.fastq.gz"}]}}],

  Gamma = #{"compareToCTRL" => {lam, {sign, [{param, "somaticVCF", false}],
                                            [{param, "tumorParts", true},
                                             {param, "ctrlBam", false}]},
                                     {forbody, bash, "blub"}},
            "bwa-mem" => {lam, {sign, [{param, "bamout", false}],
                                      [{param, "fastq", false}]},
                                {forbody, bash, "bla"}}
                                     },
  Theta = {#{}, fun sem:mu/1, Gamma, #{}},

  ?assertMatch(
    [{app,1,
          {lam,{sign,[{param,"somaticVCF",false}],
                     [{param,"tumorParts",true},{param,"ctrlBam",false}]},
               {forbody,bash,"blub"}},
          #{"ctrlBam" := [{select,1,{fut,1,[{param,"bamout",false}]}}],
            "tumorParts" := [{select,1,{fut,_,[{param,"bamout",false}]}}]}}],
    sem:eval( X, Theta ) ).







% deftask bowtie2-align( sam( File ) : [fastq1( File ) fastq2( File )] )in bash *{
%   sam=bowtie2.sam
%   tar xf $idx
%   bowtie2 -D 5 -R 1 -N 0 -L 22 -i S,0,2.50 \
%   -p 1 \
%   --no-unal -x bt2idx -1 $fastq1 -2 $fastq2 -S $sam
%   rm bt2idx.*
% }*
%
% deftask per-fastq( sam : [fastq1( File ) fastq2( File )] ) {
%   sam = bowtie2-align(
%     fastq1: fastq1,
%     fastq2: fastq2 );
% }
%
% fastq1 = "SRR359188_1.filt.fastq";
% fastq2 = "SRR359188_2.filt.fastq";
%
% sam = per-fastq(
%   fastq1: fastq1,
%   fastq2: fastq2 );
%
% sam;

marc_test() ->

  X = [{var,"sam"}],

  Rho = #{"fastq2"=>[{str,"SRR359188_2.filt.fastq"}],
          "sam"   =>[{app,1,{var,"per-fastq"},
                        #{"fastq2"=>[{var,"fastq2"}],
                          "fastq1"=>[{var,"fastq1"}]}}],
          "fastq1"=>[{str,"SRR359188_1.filt.fastq"}]
         },

  Gamma = #{"bowtie2-align"=>{lam,{sign,[{param,"sam",false}],
                                      [{correl,["fastq1","fastq2"]}]},
                                {forbody,bash,"blub"}},
            "per-fastq"    =>{lam,{sign,[{param,"sam",false}],
                                      [{correl,["fastq1","fastq2"]}]},
                                {natbody,#{"sam"=>[{app,1,{var,"bowtie2-align"},
                                                        #{"fastq2"=>[{var,"fastq2"}],
                                                          "fastq1"=>[{var,"fastq1"}]}}]}}}
           },

  Theta = {Rho, fun sem:mu/1, Gamma, #{}},

  ?assertMatch( [{select,1,{fut,_,[{param,"sam",false}]}}], sem:eval( X, Theta ) ).
  

