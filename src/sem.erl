%% -*- erlang -*-
%%
%% Computation Semantics of the Functional Scientific Workflow Language
%% Cuneiform
%%
%% Copyright 2016 Jörgen Brandt, Wolfgang Reisig, and Ulf Leser
%%
%% Licensed under the Apache License, Version 2.0 (the "License");
%% you may not use this file except in compliance with the License.
%% You may obtain a copy of the License at
%%
%%    http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing, software
%% distributed under the License is distributed on an "AS IS" BASIS,
%% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
%% See the License for the specific language governing permissions and
%% limitations under the License.

-module( sem ).
-author( "Jorgen Brandt <brandjoe@hu-berlin.de>" ).

-export( [aug/2, aug_lst/2, enum/1, eval/2, mu/1, psing/1, pnormal/1, pen/1, corrstep/3] ).

%% =========================================================
%% Sandbox
%% =========================================================

-spec mu( A::sem:app() ) -> sem:fut().

mu( {app, _C, {lam, {sign, Lo, Li}, _B}, _Fa} ) ->

  IsParam = fun( {param, _N, _Pl} ) -> true;
               ( {correl, _Lc} )    -> false
            end,

  case lists:all( IsParam, Li ) of
    false -> error( invalid_correl );
    true  -> {fut, rand:uniform( 1000000000 ), Lo}
  end.


%% =========================================================
%% Abstract Syntax
%% =========================================================

%% Expression %% ===========================================

-type expr()    :: str() | var() | select() | cnd() | app().                    % (1)
-type str()     :: {str, S::string()}.                                          % (2)
-type var()     :: {var, N::string()}.                                          % (3)
-type param()   :: {param, N::string(), Pl::boolean()}.                         % (4)
-type fut()     :: {fut, R::pos_integer(), Lo::[param()]}.                      % (5)
-type select()  :: {select, C::pos_integer(), U::fut()}.                        % (6)
-type cnd()     :: {cnd, Xc::[expr()], Xt::[expr()], Xe::[expr()]}.             % (7)
-type app()     :: {app, C::pos_integer(), Lambda::lam() | var(),               % (8)
                         Fa::#{string() => [expr()]}}.

%% Task Signature %% =======================================

-type correl()  :: {correl, Lc::[string()]}.                                    % (9)
-type inparam() :: param() | correl().                                          % (10)
-type sign()    :: {sign, Lo::[param()], Li::[inparam()]}.                      % (11)

%% Lambda Term %% ==========================================

-type lam()     :: {lam, S::sign(), B::body()}.                                 % (12)

% Task Body
-type body()    :: natbody() | forbody().                                       % (13)
-type natbody() :: {natbody, Fb::#{string() => [expr()]}}.                      % (14)
-type forbody() :: {forbody, L::lang(), S::string()}.                           % (15)
-type lang()    :: bash | perl | python | r.                                    % (16)

%% Evaluation Context %% ===================================

-type ctx()     :: {Rho   :: #{string() => [expr()]},                           % (17)
                    Mu    :: fun( ( app() ) -> fut() ),
                    Gamma :: #{string() => lam()},
                    Omega :: #{{N::string(), R::pos_integer()} => [expr()]}}.


%% =========================================================
%% Predicates
%% =========================================================

%% Normal Form %% ==========================================

-spec pnormal( X ) -> boolean()                                                 % (18)
when X :: #{string() => [expr()]} | [expr()] | expr().

pnormal( F ) when is_map( F )  -> pnormal( maps:values( F ) );                  % (19)
pnormal( L ) when is_list( L ) -> lists:all( fun pnormal/1, L );                % (20,21)
pnormal( {str, _} )            -> true;                                         % (22)
pnormal( _ )                   -> false.

%% Singularity %% ==========================================

-spec psing( A::app() ) -> boolean().                                           % (61)

psing( {app, _, {lam, {sign, _, []}, _}, _} ) -> true;                          % (62)
psing( {app, C, {lam, {sign, Lo, [{param, _, Pl}|T]}, B}, Fa} ) when Pl ->      % (63)
  psing( {app, C, {lam, {sign, Lo, T}, B}, Fa} );
psing( {app, C, {lam, {sign, Lo, [{param, N, _Pl}|T]}, B}, Fa} ) ->             % (64)
  case length( maps:get( N, Fa ) ) of
    1 -> psing( {app, C, {lam, {sign, Lo, T}, B}, Fa} );
    _ -> false
  end;
psing( _ ) -> false.

%% Enumerability %% ========================================

-spec pen( X::expr()|[expr()] ) -> boolean().                                   % (65)

pen( X )when is_list( X ) -> lists:all( fun pen/1, X );                         % (66,67)
pen( {str, _} )           -> true;                                              % (68)
pen( {cnd, _, Xt, Xe} ) when length( Xt ) =:= 1, length( Xe ) =:= 1 ->          % (69)
  pen( Xt ) andalso pen( Xe );
pen( X={app, C, {lam, {sign, Lo, _}, _}, _} ) ->                                % (70)
  case psing( X ) of
    false -> false;
    true ->
      {param, _, Pl} = lists:nth( C, Lo ),
      not Pl
  end;
pen( {select, C, {fut, _R, Lo}} ) ->                                            % (71)
  {param, _N, Pl} = lists:nth( C, Lo ),
  not Pl;
pen( _ ) -> false.

%% Context Independence %% =================================

-spec pindep( X ) -> boolean()                                                  % (81)
when X :: #{string() => [expr()]} | [expr()] | expr().

pindep( Fa ) when is_map( Fa ) -> pindep( maps:values( Fa ) );                  % (82)
pindep( X ) when is_list( X )  -> lists:all( fun pindep/1, X );                 % (83,84)
pindep( {str, _} )             -> true;                                         % (85)
pindep( {select, _, _} )       -> true;                                         % (86)
pindep( {cnd, Xc, Xt, Xe} )    ->                                               % (87)
  pindep( Xc ) andalso pindep( Xt ) andalso pindep( Xe );
pindep( {app, _, _, Fa} )      -> pindep( Fa );                                 % (88)
pindep( _ )                    -> false.


%% =========================================================
%% Evaluation
%% =========================================================

-spec eval( X::[expr()], Theta::ctx() ) -> [expr()].

eval( X, Theta ) ->
  X1 = step( X, Theta ),
  case X1 of
    X -> X;
    _ -> eval( X1, Theta )
  end.

%% The Step Relation %% ======================================

-spec step( X, Theta ) -> #{string() => [expr()]} | [expr()]
when X     :: #{string() => [expr()]} | [expr()] | expr(),
     Theta :: ctx().

% Argument map

step( F, Theta ) when is_map( F ) ->                                            % (23,24)
  maps:map( fun( _, X ) -> step( X, Theta ) end, F );

% Expression List
step( X, Theta ) when is_list( X ) ->                                           % (25,26)
  lists:flatmap( fun( Y ) -> step( Y, Theta ) end, X );

% String Literal
step( X={str, _}, _ ) -> [X];                                                   % (27)

% Variable
step( {var, N}, {Rho, _Mu, _Gamma, _Omega} ) ->                                 % (28)
  maps:get( N, Rho );

% Future Channel Selection
step( S={select, C, {fut, R, Lo}}, {_Rho, _Mu, _Gamma, Omega} ) ->              % (29,30)
  {param, N, _Pl} = lists:nth( C, Lo ),
  maps:get( {N, R}, Omega, [S] );

% Conditional
step( {cnd, [], _, Xe}, _ ) -> Xe;                                              % (31)
step( {cnd, Xc=[_|_], Xt, Xe}, Theta ) ->
  case pnormal( Xc ) of
    false -> [{cnd, step( Xc, Theta ), Xt, Xe}];                                % (32)
    true  -> Xt                                                                 % (33)
  end;

% Application (early enumeration and tail recursion)
step( {app, C, {var, N}, Fa}, {_Rho, _Mu, Gamma, _Omega} ) ->                   % (34)
  [{app, C, maps:get( N, Gamma ), Fa}];

step( X={app, C, Lambda={lam, S={sign, Lo, _}, B}, Fa},
      Theta={_, Mu, Gamma, Omega} ) ->
  case psing( X ) of
    false -> enum( [{app, C, Lambda, step( Fa, Theta )}] );                     % (89)
    true  ->
      case B of
        {forbody, _L, _Z} ->
          case pnormal( Fa ) of
            false -> [{app, C, Lambda, step( Fa, Theta )}];                     % (90)
            true  -> [{select, C, apply( Mu, [X] )}]                            % (91)
          end;
        {natbody, Fb} ->
          case pindep( Fa ) of
            false -> [{app, C, Lambda, step( Fa, Theta )}];                     % (92)
            true  ->                                              
              {param, N, Pl} = lists:nth( C, Lo ),
              #{N := V0} = Fb,
              V1 = step( V0, {maps:merge( Fb, Fa ), Mu, Gamma, Omega} ),
              case pindep( V1 ) of
                false -> [{app, C, {lam, S, {natbody, Fb#{ N => V1}}}, Fa}];    % (93)
                true  ->
                  case Pl orelse length( V1 ) =:= 1 of
                    true  -> V1;                                                % (94)
                    false -> error( output_sign_mismatch )
                  end
              end
          end
      end
  end.



%% =========================================================
%% Enumeration
%% =========================================================

%% The enum Function %%

-spec enum( A::[app()] ) -> [app()].                                            % (40)

enum( Z ) ->
  Z1 = estep( Z ),
  case Z1 of
    Z -> Z;                                                                     % (41)
    _ -> enum( Z1 )                                                             % (42)
  end.

%% Enumeration Rules (early enumeration) %%

-spec estep( A ) -> [app()]                                                     % (43)
when A :: app() | [app()].

estep( A ) when is_list( A ) ->                                                 % (44,45)
  lists:flatmap( fun( B ) -> estep( B ) end, A );
estep( X={app, _, {lam, {sign, _, []}, _}, _} ) -> [X];                         % (46)
estep( {app, C, {lam, {sign, Lo, [H={param, _N, Pl}|T]}, B}, Fa} ) when Pl ->   % (47)
  aug_lst( estep( {app, C, {lam, {sign, Lo, T}, B}, Fa} ), H );
estep( X={app, C, {lam, {sign, Lo, Li=[H={param, N, _Pl}|T]}, B}, Fa} ) ->
  #{N := V} = Fa,
  case pen( V ) of
    true  ->
      case length( V ) of
        1 -> aug_lst( estep( {app, C, {lam, {sign, Lo, T}, B}, Fa} ), H );      % (72)
        _ -> [{app, C, {lam, {sign, Lo, Li}, B}, Fa#{N => [Y]}} || Y <- V]      % (73)
      end;
    false -> [X]                                                                % (74)
  end;
estep( X={app, C, {lam, {sign, Lo, [H={correl, Lc}|T]}, B}, Fa} )
when length( Lc ) > 1 ->
  Pen = pen( [maps:get( N, Fa ) || N <- Lc] ),
  case Pen of
    false -> [X];                                                               % (75)
    true  ->
      Z = corr( Lc, Fa ),
      aug_lst( [{app, C, {lam, {sign, Lo, T}, B}, G} || G <- Z], H )            % (76)
  end.



%% Augmentation %%

-spec aug_lst( Z::[app()], A::inparam() ) -> [app()].                           % (50)

aug_lst( Z, A ) -> [aug( X, A ) || X <- Z].                                     % (51)

-spec aug( X::app(), A::inparam() ) -> app().                                   % (52)

aug( {app, C, {lam, {sign, Lo, Li}, B}, Fa}, A={param, _, _} ) ->               % (53)
  {app, C, {lam, {sign, Lo, [A|Li]}, B}, Fa};
aug( {app, C, {lam, {sign, Lo, Li}, B}, Fa}, {correl, Lc} ) ->                  % (54)
  L1 = [{param, N, false} || N <- Lc],
  {app, C, {lam, {sign, Lo, L1++Li}, B}, Fa}.

%% Correlation %%

-spec corr( Lc, F ) -> [#{string() => [expr()]}]                                % (55)
when Lc :: [string()],
     F  :: #{string() => [expr()]}.

corr( Lc=[H|_], F ) ->
  case maps:get( H, F ) of
    []    -> [];                                                                % (56)
    _     ->
      {Fstar, Fminus} = corrstep( Lc, F, F ),
      [Fstar|corr( Lc, Fminus )]                                                % (57)
  end.
  

-spec corrstep( Lc, Fstar, Fminus ) ->                                          % (58)
  {#{string() => [expr()]}, #{string() => [expr()]}}
when Lc     :: [string()],
     Fstar  :: #{string() => [expr()]},
     Fminus :: #{string() => [expr()]}.

corrstep( [], Fstar, Fminus )    -> {Fstar, Fminus};                            % (59)

corrstep( [H|T], Fstar, Fminus ) ->                                             % (60)
  #{H := [A|B]} = Fminus,
  corrstep( T, Fstar#{H => [A]}, Fminus#{H => B} ).

