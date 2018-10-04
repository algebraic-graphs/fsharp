namespace Alga.FSharp

[<RequireQualifiedAccess>]
module Map =

    /// Return all keys of the map.
    let keys m = m |> Map.toSeq |> Seq.map fst

    /// The set of all keys of the map.
    let keysSet m = m |> keys |> Set.ofSeq

    /// A map with a single element.
    let singleton k v = Map.empty |> Map.add k v

    /// Union with a combining function.
    let unionWith f m1 m2 =
        Map.fold (fun m k v -> Map.add k (match Map.tryFind k m with None -> v | Some v' -> f v v') m) m1 m2

    /// The union of a list of maps, with a combining operation: (unionsWith f == foldl (unionWith f) empty).
    let unionsWith f ms =
        Seq.fold (unionWith f) Map.empty ms

    /// The expression (isSubmapOfBy f t1 t2) returns true if all keys in t1 are in tree t2, and when f returns true when applied to their respective values.
    let isSubmapOfBy (f : 'v1 -> 'v2 -> bool) (m1 : Map<'k, 'v1>) (m2 : Map<'k, 'v2>) : bool =
        m1 |> Map.forall (fun k v1 -> match Map.tryFind k m2 with | None -> false | Some v2 -> f v1 v2)

    /// Build a map from a set of keys and a function which for each key computes its value.
    let fromSet (f : 'k -> 'v) (keys : 'k Set) : Map<'k, 'v> =
        keys |> Seq.map (fun k -> k, f k) |> Map.ofSeq

    /// Update a value at a specific key with the result of the provided function. When the key is not a member of the map, the original map is returned.
    let adjust (f : 'a -> 'a) (k : 'k) (m : Map<'k, 'a>) : Map<'k, 'a> =
        match m |> Map.tryFind k with
        | Some v -> m |> Map.add k (f v)
        | None -> m

    /// mapKeysWith c f s is the map obtained by applying f to each key of s.
    /// The size of the result may be smaller if f maps two or more distinct keys to the same new key.
    /// In this case the associated values will be combined using c. The value at the greater of the two original keys is used as the first argument to c.
    let mapKeysWith (f : 'a -> 'a -> 'a) (g : 'k1 -> 'k2) (m : Map<'k1, 'a>) : Map<'k2, 'a> =
        m
        |> Map.toSeq
        |> Seq.map (fun (k, v) -> g k, v)
        |> Seq.groupBy fst
        |> Seq.map (fun (k, vs) -> k, vs |> Seq.map snd |> Seq.reduce f)
        |> Map.ofSeq
