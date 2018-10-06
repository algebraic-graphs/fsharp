namespace Alga.FSharp

/// Non-empty, possibly infinite, multi-way trees; also known as rose trees.
type 'a Tree =
    {
        RootLabel : 'a
        SubForest : 'a Forest
    }

and 'a Forest = 'a Tree list

[<RequireQualifiedAccess>]
module Tree =

    let rec map (f : 'a -> 'b) (t : 'a Tree) : 'b Tree =
        {
            RootLabel = f t.RootLabel
            SubForest = List.map (map f) t.SubForest
        }

    /// Returns the elements of a tree in pre-order.
    let rec flatten (t : 'a Tree) : 'a seq =
        seq {
            yield t.RootLabel
            for t in t.SubForest do yield! flatten t
        }

    let toList (t : 'a Tree) : 'a list =
        t |> flatten |> List.ofSeq
