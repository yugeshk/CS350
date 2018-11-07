declare SAS C
SAS = {Dictionary.new}
{NewCell 0 ?C}

fun {AddKeyToSAS}
  {Browse 'AddKeyToSAS'}
  C:=@C+1
  {Dictionary.put SAS @C equivalence(@C)}
  @C
end

fun {RetrieveFromSAS Key}
  {Browse 'RetrieveFromSAS'}
  {Dictionary.get SAS Key ?} 
end

proc {BindValueToKeyInSAS Key Val}
  {Browse 'BindValueToKeyInSAS'}
  local Value in
    {Dictionary.get SAS Key Value}
    case Value
    of equivalence(X) then {Dictionary.put SAS Key Val}
    else {Exception.'raise' alreadyAssigned(Key Val {Dictionary.get SAS Key ?})}
    end 
  end
end

proc {BindRefToKeyInSAS Key RefKey}
  {Browse 'BindRefToKeyInSAS'}
  local Value in
    {Dictionary.get SAS Key Value}
    case Value
    of equivalence(X) then {Dictionary.put SAS Key reference(RefKey)}
    else {Exception.'raise' alreadyAssigned2(Key {Dictionary.get SAS Key ?})}
    end 
  end
end

% Helper functions not part of the assgnment

proc {PrintAll Current}
  if Current > @C then {Browse 'Done'} else {Browse {Dictionary.get SAS Current ?}} {PrintAll Current+1} end
end