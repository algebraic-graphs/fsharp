namespace Alga.FSharp

[<RequireQualifiedAccess>]
module Map =

    let keys m = m |> Map.toSeq |> Seq.map fst

    let keysSet m = m |> keys |> Set.ofSeq

    let singleton k v = Map.empty |> Map.add k v

    let unionWith f m1 m2 =
        Map.fold (fun m k v -> Map.add k (match Map.tryFind k m with None -> v | Some v' -> f v v') m) m1 m2

    let unionsWith f ms =
        Seq.fold (unionWith f) Map.empty ms

    let isSubmapOfBy (f : 'v1 -> 'v2 -> bool) (m1 : Map<'k, 'v1>) (m2 : Map<'k, 'v2>) : bool =
        m1 |> Map.forall (fun k v1 -> match Map.tryFind k m2 with | None -> false | Some v2 -> f v1 v2)

    let fromSet (f : 'k -> 'v) (keys : 'k Set) : Map<'k, 'v> =
        keys |> Seq.map (fun k -> k, f k) |> Map.ofSeq
