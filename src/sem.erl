%% -*- erlang -*-
%%
%% Cuneiform: A Functional Language for Large Scale Scientific Data Analysis
%%
%% Copyright 2016 Jörgen Brandt, Marc Bux, and Ulf Leser
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

-export( [aug/2, aug_argpair/2, enum_app/1, eval/2, mu/1, psing/1, pfinal/1, pen/1, corrstep/3] ).

%% =========================================================
%% Sandbox
%% =========================================================

-spec mu( A::sem:app() ) -> sem:fut().

mu( {app, _C, {lam, {sign, Lo, _Li}, _B}, _Fa} ) ->
  {fut, random:uniform( 1000000000 ), Lo}.


%% =========================================================
%% Abstract Syntax
%% =========================================================

%% Expression %% ===========================================

-type expr()    :: str() | var() | select() | cnd() | app().                    % (1)
-type str()     :: {str, S::string()}.                                          % (2)
-type var()     :: {var, N::string()}.                                          % (3)
-type select()  :: {select, C::pos_integer(), U::fut()}.                        % (4)
-type fut()     :: {fut, R::pos_integer(), Lo::[param()]}.                      % (5)
-type cnd()     :: {cnd, Xc::[expr()], Xt::[expr()], Xe::[expr()]}.             % (6)
-type app()     :: {app, C::pos_integer(), Lambda::lam() | var(),               % (7)
                         Fa::#{string() => [expr()]}}.

%% Lambda %% ===============================================

-type lam()     :: {lam, S::sign(), B::body()}.                                 % (8)

% Task Signature
-type sign()    :: {sign, Lo::[param()], Li::[inparam()]}.                      % (9)
-type param()   :: {param, N::string(), Pl::boolean()}.                         % (10)
-type inparam() :: param() | correl().                                          % (11)
-type correl()  :: {correl, Lc::[string()]}.                                    % (12)

% Body
-type body()    :: natbody() | forbody().                                       % (13)
-type natbody() :: {natbody, Fb::#{string() => [expr()]}}.                      % (14)
-type forbody() :: {forbody, L::lang(), S::string()}.                           % (15)
-type lang()    :: bash | python | r.                                           % (16)

%% Argument Pair %% ========================================

-type argpair() :: {L0::[inparam()], F::#{string() => [expr()]}}.               % (17)

%% Evaluation Context %% ===================================

-type ctx()     :: {Rho   :: #{string() => [expr()]},                           % (18)
                    Mu    :: fun( ( app() ) -> fut() ),
                    Gamma :: #{string() => lam()},
                    Omega :: #{{N::string(), R::pos_integer()} => [expr()]}}.


%% =========================================================
%% Predicates
%% =========================================================

%% Finality %% =============================================

-spec pfinal( X ) -> boolean()                                                  % (19)
when X :: #{string() => [expr()]} | [expr()] | expr().

pfinal( F ) when is_map( F )   -> pfinal( maps:values( F ) );                   % (20)
pfinal( L ) when is_list( L )  -> lists:all( fun pfinal/1, L );                 % (21,22)
pfinal( {str, _S} )            -> true;                                         % (23)
pfinal( _T )                   -> false.

%% Singularity %% ==========================================

-spec psing( A::app() ) -> boolean().                                           % (70)

psing( {app, _C, {lam, {sign, _Lo, Li}, _B}, Fa} ) ->                           % (71)
  psing_argpair( {Li, Fa} ).

-spec psing_argpair( Z::argpair() ) -> boolean().                               % (72)

psing_argpair( {[], _F} )                         -> true;                      % (73)
psing_argpair( {[{param, _N, Pl}|T], F} ) when Pl -> psing_argpair( {T, F} );   % (74)
psing_argpair( {[{param, N, _Pl}|T], F} ) ->                                    % (75)
  case length( maps:get( N, F ) ) of
    1 -> psing_argpair( {T, F} );
    _ -> false
  end;
psing_argpair( _Z ) -> false.

%% Enumerability %% ========================================

-spec pen( X::expr()|[expr()] ) -> boolean().                                   % (76)

pen( X )when is_list( X ) -> lists:all( fun pen/1, X );                         % (77,78)
pen( {str, _S} ) -> true;                                                       % (79)
pen( {cnd, _Xc, Xt, Xe} )when length( Xt ) =:= 1, length( Xe ) =:= 1 ->         % (80)
  pen( Xt ) andalso pen( Xe );
pen( X={app, C, {lam, {sign, Lo, _Li}, _B}, _Fb} ) ->                           % (81)
  case psing( X ) of
    false -> false;
    true ->
      {param, _N, Pl} = lists:nth( C, Lo ),
      not Pl
  end;
pen( {select, C, {fut, _R, Lo}} ) ->                                            % (82)
  {param, _N, Pl} = lists:nth( C, Lo ),
  not Pl;
pen( _T ) -> false.

%% Context Independence %% =================================

-spec pindep( X ) -> boolean()                                                  % (96)
when X :: #{string() => [expr()]} | [expr()] | expr().

pindep( Fa ) when is_map( Fa ) -> pindep( maps:values( Fa ) );                  % (97)
pindep( X ) when is_list( X )  -> lists:all( fun pindep/1, X );                 % (98,99)
pindep( {str, _} )             -> true;                                         % (100)
pindep( {select, _, _} )       -> true;                                         % (101)
pindep( {cnd, Xc, Xt, Xe} )    ->                                               % (102)
  pindep( Xc ) andalso pindep( Xt ) andalso pindep( Xe );
pindep( {app, _, _, Fa} )      -> pindep( Fa );                                 % (103)
pindep( _ )                    -> false.


%% =========================================================
%% Evaluation
%% =========================================================

%% The eval Function %% ====================================

-spec eval( X::[expr()], Theta::ctx() ) -> [expr()].                            % (24)

eval( X, Theta ) ->
  X1 = step( X, Theta ),
  case X1 of
    X -> X;                                                                     % (25)
    _ -> eval( X1, Theta )                                                      % (26)
  end.

%% Reduction Rules %% ======================================

-spec step_assoc( F, Theta ) -> #{string() => [expr()]}                         % (27)
when F     :: #{string() => [expr()]},
     Theta :: ctx().

step_assoc( F, Theta ) when is_map( F ) ->                                      % (28)
  maps:map( fun( _N, X ) -> step( X, Theta ) end, F ).


-spec step( X, Theta ) -> [expr()]                                              % (29)
when X     :: #{string() => [expr()]} | [expr()] | expr(),
     Theta :: ctx().


% Expression List
step( X, Theta ) when is_list( X ) ->                                           % (30,31)
  lists:flatmap( fun( Y ) -> step( Y, Theta ) end, X );

% String Literal
step( X={str, _S}, _Theta ) -> [X];                                             % (32)

% Variable
step( {var, N}, {Rho, _Mu, _Gamma, _Omega} ) ->                                 % (33)
  maps:get( N, Rho );

% Future Channel Selection
step( S={select, C, {fut, R, Lo}}, {_Rho, _Mu, _Gamma, Omega} ) ->              % (34,35)
  {param, N, _Pl} = lists:nth( C, Lo ),
  maps:get( {N, R}, Omega, [S] );

% Conditional
step( {cnd, [], _Xt, Xe}, _Theta ) -> Xe;                                       % (36)
step( {cnd, Xc=[_|_], Xt, Xe}, Theta ) ->
  case pfinal( Xc ) of
    false -> [{cnd, step( Xc, Theta ), Xt, Xe}];                                % (37)
    true  -> Xt                                                                 % (38)
  end;

% Application
step( {app, C, {var, N}, Fa}, {_Rho, _Mu, Gamma, _Omega} ) ->                   % (104)
  [{app, C, maps:get( N, Gamma ), Fa}];

step( X={app, C, Lambda={lam, S={sign, Lo, _Li}, B}, Fa},
      Theta={_Rho, Mu, Gamma, Omega} ) ->
  case psing( X ) of
    false -> enum_app( {app, C, Lambda, step_assoc( Fa, Theta )} );             % (105)
    true  ->
      case B of
        {forbody, _L, _Z} ->
          case pfinal( Fa ) of
            false -> [{app, C, Lambda, step_assoc( Fa, Theta )}];               % (106)
            true  -> [{select, C, apply( Mu, [X] )}]                            % (107)
          end;
        {natbody, Fb} ->
          case pindep( Fa ) of
            false -> [{app, C, Lambda, step_assoc( Fa, Theta )}];               % (108)
            true  ->                                              
              {param, N, Pl} = lists:nth( C, Lo ),
              #{N := V0} = Fb,
              V1 = step( V0, {maps:merge( Fb, Fa ), Mu, Gamma, Omega} ),
              case pindep( V1 ) of
                false -> [{app, C, {lam, S, {natbody, Fb#{ N => V1}}}, Fa}];    % (109)
                true  ->
                  case Pl orelse length( V1 ) =:= 1 of
                    true  -> V1;                                                % (110)
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

-spec enum_app( A::app() ) -> [app()].                                          % (45)

enum_app( {app, C, {lam, {sign, Lo, Li}, B}, Fa} ) ->                           % (46)
  [{app, C, {lam, {sign, Lo, L1}, B}, F1} || {L1, F1} <- enum( [{Li, Fa}] )].

-spec enum( Z::[argpair()] ) -> [argpair()].                                    % (47)

enum( Z ) ->
  Z1 = estep( Z ),
  case Z1 of
    Z -> Z;                                                                     % (48)
    _ -> enum( Z1 )                                                             % (49)
  end.

%% Enumeration Rules %%

-spec estep( Z::[argpair()] ) -> [argpair()].                                   % (50)

estep( Z ) ->                                                                   % (51,52)
  lists:flatmap( fun( {Li, F} ) -> estep_param_lst( Li, F ) end, Z ).

-spec estep_param_lst( Li, F ) -> [argpair()]                                   % (83)
when Li::[inparam()],
     F::#{string() => [expr()]}.

estep_param_lst( [], F ) -> [{[], F}];                                          % (84)
estep_param_lst( [H={param, _N, Pl}|T], F ) when Pl ->                          % (85)
  aug( estep_param_lst( T, F ), H );
estep_param_lst( L=[H={param, N, _Pl}|T], F ) ->
  #{N := V} = F,
  case pen( V ) of
    false -> [{L, F}];                                                          % (86)
    true  ->
      case length( V ) of
        1 -> aug( estep_param_lst( T, F ), H );                                           % (87)
        _ -> [{L, F#{N => [X]}} || X <- V]                                      % (88)
      end
  end;
estep_param_lst( L=[H={correl, Lc}|T], F ) when length( Lc ) > 1 ->
  Pen = pen( [maps:get( N, F ) || N <- Lc] ),
  case Pen of
    false -> [{L, F}];                                                          % (89)
    true  ->
      Z = corr( Lc, F ),
      aug( [{T, G} || G <- Z], H )                                              % (90)
  end.



%% Augmentation %%

-spec aug( Z::[argpair()], A::inparam() ) -> [argpair()].                       % (59)

aug( Z, A ) -> [aug_argpair( Y, A ) || Y <- Z].                                 % (60)

-spec aug_argpair( Y::argpair(), A::inparam() ) -> argpair().                   % (61)

aug_argpair( {L0, F}, A={param, _N, _Pl} ) -> {[A|L0], F};                      % (62)
aug_argpair( {L0, F}, {correl, Lc} ) ->                                         % (63)
  L1 = [{param, N, false} || N <- Lc],
  {L1++L0, F}.

%% Correlation %%

-spec corr( Lc, F ) -> [#{string() => [expr()]}]                                % (64)
when Lc :: [string()],
     F  :: #{string() => [expr()]}.

corr( Lc=[H|_], F ) ->
  case maps:get( H, F ) of
    []    -> [];                                                                % (65)
    _     ->
      {Fstar, Fminus} = corrstep( Lc, F, F ),
      [Fstar|corr( Lc, Fminus )]                                                % (66)
  end.
  

-spec corrstep( Lc, Fstar, Fminus ) ->                                          % (67)
  {#{string() => [expr()]}, #{string() => [expr()]}}
when Lc     :: [string()],
     Fstar  :: #{string() => [expr()]},
     Fminus :: #{string() => [expr()]}.

corrstep( [], Fstar, Fminus )    -> {Fstar, Fminus};                            % (68)

corrstep( [H|T], Fstar, Fminus ) ->                                             % (69)
  #{H := [A|B]} = Fminus,
  corrstep( T, Fstar#{H => [A]}, Fminus#{H => B} ).

