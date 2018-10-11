declare SemanticStack Program ExecuteStatement Execute Environment Adjoin SAS C

\insert 'SingleAssignmentStore.oz'

proc {Adjoin E X NewE}
   local T in
      T = {AddKeyToSAS}
      {AdjoinAt E X T NewE}
   end
   {Browse NewE }
end
proc {Execute S O}
   local NewE in
      case S of nil then skip
      [] X|T then case X of nil then skip
   	       [] es(s:Xs e:Xe) then case Xs of nil then skip
   				     [] nop | nil then skip
   				     [] var | ident(V) | S1 then {Adjoin Xe V NewE} {Execute es(s:S1 e:NewE) | T O} 
   				     [] S1|S2 then {Execute es(s:S1 e:Xe)|es(s:S2 e:Xe)|T O}
   				     else skip
   				     end
   	       else skip 
   	       end
      else skip
      end
   end
end 

Program = [var ident(x)
	   [var ident(y)
	    [var ident(x)
	     [nop]]]]
Environment = '#'
SemanticStack = [es(s:Program e:Environment)]
%SAS = {Dictionary.new}
%{NewCell 0 ?C}

{Execute SemanticStack SAS}
{Browse [{Dictionary.get SAS 3}]}
