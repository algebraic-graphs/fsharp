namespace Alga.FSharp

[<RequireQualifiedAccess>]
module Option =

    let guard b =
        match b with
        | true -> Some ()
        | false -> None


type OptionBuilder () =

    member __.Return a = Some a

    member __.ReturnFrom (a : 'a option) = a

    member __.Bind (a : 'a option, f : 'a -> 'b option) : 'b option =
        Option.bind f a


[<AutoOpen>]
module OptionBuilder =

    let option = OptionBuilder ()
