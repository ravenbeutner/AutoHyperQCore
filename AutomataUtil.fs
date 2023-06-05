(*    
    Copyright (C) 2022-2023 Raven Beutner

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)

module AutoHyperQCore.AutomataUtil

open System.Collections.Generic

open FsOmegaLib.SAT
open FsOmegaLib.AutomatonSkeleton
open FsOmegaLib.GNBA
open FsOmegaLib.NBA


let internal constructConjunctionOfGNBAs (autList : list<GNBA<int, 'L>>) = 
    let autList = GNBA.bringToSameAPs autList

    let sumOfAccSets = 
        (0, autList)
        ||> List.mapFold (fun s x -> 
            s, s + x.NumberOfAcceptingSets
            )
        |> fst

    let initStates = 
        autList
        |> List.map (fun x -> x.InitialStates |> seq)
        |> Util.cartesianProduct
        |> set

    let queue = new Queue<_>(initStates)

    let allStates = new HashSet<_>(initStates)
    let newEdgesDict = new Dictionary<_,_>()
    let newAccSetsDict = new Dictionary<_,_>()

    while queue.Count <> 0 do 
        let n = queue.Dequeue()
        
        let edges = 
            n 
            |> List.mapi (fun i state -> autList.[i].Edges.[state] |> seq)
            |> Util.cartesianProduct
            |> Seq.choose (fun x -> 
                let guards, sucs = List.unzip x

                let combinedGuard = DNF.constructConjunction guards

                if DNF.isSat combinedGuard then  
                    if allStates.Contains sucs |> not then 
                        allStates.Add sucs |> ignore
                        queue.Enqueue sucs
                        
                    Some (combinedGuard, sucs)
                else
                    None
            )
            |> Seq.toList

        // Ensure disjoint acceptance Sets
        let accSets = 
            n 
            |> List.mapi (fun i state -> autList.[i].AcceptanceSets.[state])
            |> List.mapi (fun i accSet -> 
                accSet |> Set.map (fun y -> y + sumOfAccSets.[i])
                )
            |> Set.unionMany
        
        newEdgesDict.Add(n, edges)
        newAccSetsDict.Add(n, accSets)

    {
        GNBA.Skeleton =
                {
                    AutomatonSkeleton.States = set allStates;
                    APs = autList.[0].APs
                    Edges = Util.dictToMap newEdgesDict
                };
        InitialStates = initStates;
        AcceptanceSets = Util.dictToMap newAccSetsDict;
        NumberOfAcceptingSets = autList |> List.map (fun x -> x.NumberOfAcceptingSets) |> List.sum;
    }
    |> GNBA.convertStatesToInt


let internal constructConjunctionOfGnbaPair (aut1 : GNBA<int, 'L>) (aut2 : GNBA<int, 'L>) = 
    let aut1, aut2 = GNBA.bringPairToSameAPs aut1 aut2

    let initStates = Seq.allPairs aut1.InitialStates aut2.InitialStates

    let queue = new Queue<_>(initStates)

    let allStates = new HashSet<_>(initStates)
    let newEdgesDict = new Dictionary<_,_>()
    let newAccSetsDict = new Dictionary<_,_>()

    while queue.Count <> 0 do 
        let s1, s2 = queue.Dequeue()
        
        let edges =
            (aut1.Edges.[s1], aut2.Edges.[s2])
            ||> Seq.allPairs
            |> Seq.choose (fun ((g1, t1), (g2, t2)) -> 
                let combinedGuard = DNF.constructConjunction [g1; g2]

                if DNF.isSat combinedGuard then  
                    if allStates.Contains (t1, t2) |> not then 
                        allStates.Add (t1, t2) |> ignore
                        queue.Enqueue (t1, t2)
                        
                    Some (combinedGuard, (t1, t2))
                else
                    None
            )
            |> Seq.toList

        // Ensure disjoint acceptance Sets
        let accSets =
            aut2.AcceptanceSets.[s2]
            |> Set.map (fun x -> x + aut1.NumberOfAcceptingSets)
            |> Set.union aut1.AcceptanceSets.[s1]
            
        newEdgesDict.Add((s1, s2), edges)
        newAccSetsDict.Add((s1, s2), accSets)

    {
        GNBA.Skeleton =
                {
                    AutomatonSkeleton.States = set allStates;
                    APs = aut1.APs
                    Edges = Util.dictToMap newEdgesDict
                };
        InitialStates = set initStates;
        AcceptanceSets = Util.dictToMap newAccSetsDict;
        NumberOfAcceptingSets = aut1.NumberOfAcceptingSets + aut2.NumberOfAcceptingSets
    }
    |> GNBA.convertStatesToInt



type Lasso<'L> = 
    {
        Prefix : list<'L>
        Loop : list<'L>
    }

module Lasso = 
    let length (lasso : Lasso<'L>)= 
        lasso.Prefix.Length + lasso.Loop.Length

let internal shortestAcceptingPaths (nba: NBA<'T, 'L>) = 
    let satEdges = 
        nba.Edges
        |> Map.map (fun _ l -> 
            l |> List.filter (fun (g, _) -> DNF.isSat g)
            )

    let res = GraphUtil.shortestPathsBetweenAllPairs nba.States (fun x -> satEdges.[x]) false 

    let a = 
        Seq.allPairs nba.InitialStates nba.AcceptingStates
        |> Seq.filter (fun (init, acc) -> (res.ContainsKey (init, acc) || init = acc) && res.ContainsKey (acc, acc))
        |> Seq.map (fun (init, acc) -> 
            {
                Lasso.Prefix = if init = acc then [] else res.[init, acc] |> fst; 
                Loop = res.[acc, acc] |> fst
            }
            )
    
    if Seq.isEmpty a then 
        None 
    else 
        a 
        |> Seq.minBy Lasso.length
        |> Some
