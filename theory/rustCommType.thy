theory rustCommType
imports
  Main
begin

datatype (set: 'a, 'b) Result =
    Ok 'a
  | Err 'b

end