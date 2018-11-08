declare SemanticStack Program ExecuteStatement Execute Environment Adjoin SAS C

%\insert 'SingleAssignmentStore.oz'
\insert 'Unify.oz'

proc {Adjoin E X NewE}
   local T in
      T = {AddKeyToSAS}
      {AdjoinAt E X T NewE}
   end
end

fun {CheckTrue Id Env Sas}
   local Temp in
     case Id of nil then Temp = false
     [] ident(X) then Temp = {RetrieveFromSAS Env.X}
     else Temp = Id
     end

     case Temp of nil then false
     [] literal(L) then L\=0 orelse L == true
     [] reference(Y) then {CheckTrue {RetrieveFromSAS Y} Env Sas}
     else false
     end
   end
end

fun {CheckPattern Id Pattern Env Sas}
  local Temp in
    case Id of nil then Temp = false
    [] ident(X) then Temp = {RetrieveFromSAS Env.X}
    else Temp = Id
    end

    case Temp of nil then false
    [] literal(L) then false
    [] reference(Y) then {CheckPattern {RetrieveFromSAS Y} Pattern Env Sas}
    [] record|Record1Label|Record1FeaturePairs|nil then
       case Pattern of nil then false
       [] record|Record2Label|Record2FeaturePairs|nil then
          if Record1Label == Record2Label andthen {IsAritySame Record1FeaturePairs Record2FeaturePairs} then true %TODO WE are following the book, might be a problem
          else false
          end
       else false
       end
    else false
    end
  end
end

fun {BadSearchDict Pattern Sas ToPair}
  local Temp in
    {List.filter {Dictionary.entries Sas ?} fun {$ Entry} case Entry of Key#Value then Value == Pattern else false end end Temp}
    %{Browse 'BadSearchDict'#Temp}
    case Temp of nil then badsituation#nil
    else case Temp.1 of nil then badsituation2#nil
         [] K#V then ToPair#K
         else badsituation3#nil
         end
    end
  end
end

proc {AdjoinPattern Id Pattern Env NewEnv Sas}
  local Temp in
    case Id of nil then Temp = false
    [] ident(X) then Temp = {RetrieveFromSAS Env.X}
    else Temp = Id
    end

    case Temp of nil then skip
    [] literal(L) then skip
    [] reference(Y) then {AdjoinPattern {RetrieveFromSAS Y} Pattern Env NewEnv Sas}
    [] record|Record1Label|Record1FeaturePairs|nil then
       case Pattern of nil then skip
       [] record|Record2Label|Record2FeaturePairs|nil then
          if Record1Label == Record2Label andthen {IsAritySame Record1FeaturePairs Record2FeaturePairs} then
              {AdjoinList Env
                {List.zip Record1FeaturePairs Record2FeaturePairs 
                    fun {$ FeaturePair1 FeaturePair2}
                      {Browse 'badsituationChecker'#FeaturePair1#FeaturePair2}
                      case FeaturePair2.2.1 of ident(PatternFeat) then
                          case FeaturePair1.2.1 of equivalence(CheckedVariableFeatEq) then PatternFeat#CheckedVariableFeatEq
                          [] reference(CheckedVariableFeatRef) then PatternFeat#CheckedVariableFeatRef
                          else {BadSearchDict FeaturePair1.2.1 Sas PatternFeat}
                          end
                      else badsituation#nil
                      end
                    end
                ?} 
              NewEnv}
          else skip
          end
       else skip
       end
    else skip
    end
  end
end

fun {CheckProcedure Id ParameterList Env Sas}
  local Temp in
    case Id of nil then Temp = false
    [] ident(X) then Temp = {RetrieveFromSAS Env.X}
    else Temp = Id
    end

    case Temp of nil then false
    [] reference(Y) then {CheckProcedure {RetrieveFromSAS Y} ParameterList Env Sas}
    [] procedure|ParamList|Statements|CEnv|nil then 
        {Browse 'CheckingApply'#ParamList#Statements#CEnv}
        if {List.length ParamList ?} == {List.length ParameterList ?} then {Browse 'Valid Application'} true else false end
    else false
    end
  end
end

proc {GetEnvAndStatements Id ParameterList Env NewEnv NewStatements Sas}
  local Temp in
    case Id of nil then Temp = false
    [] ident(X) then Temp = {RetrieveFromSAS Env.X}
    else Temp = Id
    end

    case Temp of nil then skip
    [] reference(Y) then {GetEnvAndStatements {RetrieveFromSAS Y} ParameterList Env NewEnv NewStatements Sas}
    [] procedure|ParamList|Statements|CEnv|nil then 
        {Browse 'Applying'#ParamList#Statements#CEnv}
        % Bad naming - ParamList is the formal arguments in the definition, ParameterList is the list on call
        if {List.length ParamList ?} == {List.length ParameterList ?} then
            NewStatements = Statements
            {AdjoinList CEnv
              {List.zip ParamList ParameterList
                  fun {$ FormalArg ActualArg}
                    case FormalArg of nil then badsituation#nil
                    [] ident(FA) then case ActualArg of nil then badsituation#nil
                                      [] ident(AA) then FA#Env.AA
                                      else badsituation#nil
                                      end
                    else badsituation#nil
                    end
                  end
              ?}
            NewEnv}

        else
            skip
        end
    else skip
    end
  end
end

proc {Execute S O}
   local NewE NewS in
      case S of nil then skip
      [] X|T then case X of nil then skip
   	       [] es(s:Xs e:Xe) then %{Browse Xs} 
                    case Xs of nil then skip
   				          [] [nop]then {Execute T O}
   				          [] [var ident(V) S1] then {Adjoin Xe V NewE} {Execute es(s:S1 e:NewE)|T O}

                    [] [bind ident(V1) ident(V2)] then {Browse 'var var bind'} {Unify ident(V1) ident(V2) Xe} {Execute T O}
                    [] [bind ident(V1) procedure|ParamList|Statements|nil] then {Browse 'Proc'#ParamList#Statements} {Unify ident(V1) [procedure ParamList Statements Xe] Xe} {Execute T O}
                    [] [bind procedure|ParamList|Statements|nil ident(V1)] then {Browse 'Proc'#ParamList#Statements} {Unify ident(V1) [procedure ParamList Statements Xe] Xe} {Execute T O}
                    [] [bind ident(V1) V2] then {Browse 'var val bind'} {Unify ident(V1) V2 Xe} {Execute T O} %This split for bind is purely convinience
                    [] [bind V2 ident(V1)] then {Browse 'val var bind'} {Unify ident(V1) V2 Xe} {Execute T O} %This split for bind is purely convinience

                    [] apply|ParamList then {Browse 'Apply'#ParamList} 
                          if {CheckProcedure ParamList.1 ParamList.2 Xe O} then
                              {Browse 'Proc Applied'}
                              {GetEnvAndStatements ParamList.1 ParamList.2 Xe NewE NewS O}
                              {Execute es(s:NewS e:NewE)|T O} 
                          else 
                              {Raise invalidProcApplication(ParamList.1)}
                          end
                    [] [conditional ident(X) S1 S2] then {Browse 'MatchCheck'#Xe.X}
                          if {CheckTrue ident(X) Xe O} then
                              {Browse 'True'}
                              {Execute es(s:S1 e:Xe)|T O}
                          else
                              {Browse 'False'}
                              {Execute es(s:S2 e:Xe)|T O}
                          end
   				          [] [match ident(X) P1 S1 S2] then
                          if {CheckPattern ident(X) P1 Xe O} then
                              {Browse 'PTrue'}
                              {AdjoinPattern ident(X) P1 Xe NewE O}
                              {Execute es(s:S1 e:NewE)|T O}
                          else
                              {Browse 'PFalse'}
                              {Execute es(s:S2 e:Xe)|T O}
                          end
                    %[] S1|S2|nil then {Execute es(s:S1 e:Xe)|es(s:S2 e:Xe)|T O}
                    [] S1|S2 then {Browse S1} {Execute es(s:S1 e:Xe)|es(s:S2 e:Xe)|T O}
   				     else {Browse 'Problem'} skip
   				     end
   	       else skip
   	       end
      else skip
      end
   end
end



%Program = 
%[var ident(x)
%  [var ident(y)
%    [var ident(z)
%      [
%        [bind ident(y) literal(0)]
%        [bind ident(z) literal(1)]
%        [bind ident(x) [procedure [ident(a) ident(b)] [ [conditional ident(b) [nop] [nop] ] ] ]]
%        [apply ident(x) ident(y) ident(z)]
%      ]
%    ]
%  ]
%]
%Program = 
%[var ident(x)
%	[var ident(y)
%    [var ident(z)
%      [ 
%        [bind ident(y) literal(0)]
%        [bind ident(x) [record literal(a) [[literal(b) ident(y)] [literal(c) ident(y)] ]]]
%        [
%          match ident(x) [record literal(a) [[literal(b) ident(p)] [literal(c) ident(q)] ]]
%          [conditional ident(q) [nop] [nop]] 
%          [nop]
%        ]
%      ]
%    ]
%  ]
%]

Environment = '#'
SemanticStack = [es(s:Program e:Environment)]

{Execute SemanticStack SAS}
{PrintAll 1}