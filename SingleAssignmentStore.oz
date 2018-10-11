declare SAS C
SAS = {Dictionary.new}
{NewCell 0 ?C}

fun {AddKeyToSAS}
    C:=@C+1
    {Dictionary.put SAS @C nil}
    @C
end

fun {RetriveKeyFromSAS Key}
  5
end