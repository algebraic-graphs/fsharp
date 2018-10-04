namespace Alga.FSharp

type 'a Tree =
    {
        RootLabel : 'a
        SubForest : 'a Forest
    }

and 'a Forest = 'a Tree list
