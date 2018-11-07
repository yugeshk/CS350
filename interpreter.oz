declare SemanticStack Program ExecuteStatement Execute Environment Adjoin SAS C

%\insert 'SingleAssignmentStore.oz'
\insert 'Unify.oz'

proc {Adjoin E X NewE}
   local T in
      T = {AddKeyToSAS}
      {AdjoinAt E X T NewE}
   end
   {Browse NewE }
end

fun {CheckTrue Id Env Sas}
   case Id of nil then false
   [] ident(X) then
      local Temp in 
         Temp = {RetrieveFromSAS Env.X}
         case Temp of nil then false
         [] literal(L) then L\=0
         else false
         end
      end
   else false
   end
end

proc {Execute S O}
   local NewE in
      case S of nil then skip
      [] X|T then case X of nil then skip
   	       [] es(s:Xs e:Xe) then {Browse Xs} case Xs of nil then skip
   				     [] [nop]then {Execute T O}
   				     [] [var ident(V) S1] then {Adjoin Xe V NewE} {Execute es(s:S1 e:NewE)|T O}
                    [] [bind ident(V1) ident(V2)] then {Browse 'var var bind'} {Unify ident(V1) ident(V2) Xe} {Execute T O}
                    [] [bind ident(V1) V2] then {Browse 'var val bind'} {Unify ident(V1) V2 Xe} {Execute T O} %This split for bind is purely convinience
                    [] [conditional ident(X) S1 S2] then if {CheckTrue ident(X) Xe O} then {Browse 'True'} {Execute es(s:S1 e:Xe)|T O} else {Browse 'False'} {Execute es(s:S2 e:Xe)|T O} end
   				     %[] S1|S2|nil then {Execute es(s:S1 e:Xe)|es(s:S2 e:Xe)|T O}
                    [] [S1 S2] then {Execute es(s:S1 e:Xe)|es(s:S2 e:Xe)|T O}
   				     else skip
   				     end
   	       else skip 
   	       end
      else skip
      end
   end
end 

Program = 
[var ident(x)
	[var ident(y)
	  [var ident(x)
	     [[bind ident(x) literal(1)] [conditional ident(x) [nop] [nop]]]
      ]
   ]
]
%Program = [[nop] [nop] [nop]]
Environment = '#'
SemanticStack = [es(s:Program e:Environment)]
%SAS = {Dictionary.new}
%{NewCell 0 ?C}

{Execute SemanticStack SAS}
{PrintAll 1}