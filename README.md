**This is infrastructure code. If you just want to start using protocol buffers in Lean, start 
[here](https://github.com/zygi/lean-protoc-compiler).**

The runtime part of the Lean 4 third-party protocol buffer implementation. Most of this package
contains infrastructure code that users shouldn't have to care about. The relevant parts are the
interfaces that generated code will implement:

```lean
class ProtoEnum (α: Type u) where
  toInt : α -> Int
  ofInt : Int -> Option α

class ProtoSerialize (α: Type u) where
  serialize : α -> Except IO.Error ByteArray
  serializeToHex : α -> Except IO.Error String := fun a => Utils.byteArrayToHex <$> (serialize a)

class ProtoDeserialize (α: Type u) where
  deserialize : ByteArray -> Except IO.Error α
  deserializeFromHex : String -> Except IO.Error α := fun x => do
    match Utils.hexToByteArray x with
    | none => Except.error $ IO.userError "Failed to parse hex string"
    | some val => deserialize val 
```

This is not a Google product. 