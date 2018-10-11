declare SemanticStack Program ExecuteStatement Execute Environment SAS Adjoin AddSAS C

{NewCell 0 ?C}

fun {AddSAS}
   C:=@C+1
   @C
end

fun {Adjoin E X}
   local T in
      T = {AddSAS}
      {Dictionary.put E X T}
   end
   {Browse {Dictionary.entries E ?}}
   E
end
proc {Execute S O}
   case S of nil then skip
   [] X|T then case X of nil then skip
	       [] es(s:Xs e:Xe) then case Xs of nil then skip
				     [] nop | nil then skip
				     [] var | ident(V) | S1 then {Execute es(s:S1 e:{Adjoin Xe V}) | T O} 
				     [] S1|S2 then {Execute es(s:S1 e:Xe)|es(s:S2 e:Xe)|T O}
				     else skip
				     end
	       else skip 
	       end
   else skip
   end
end 

Program = [var ident(x)
	   [var ident(y)
	    [var ident(x)
	     [nop]]]]
Environment = {Dictionary.new}
SemanticStack = [es(s:Program e:Environment)]

{Execute SemanticStack SAS}
{Browse SAS}
