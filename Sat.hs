-- A Very Small SAT Solver
-- https://web.archive.org/web/20201109101535/http://www.cse.chalmers.se/~algehed/blogpostsHTML/SAT.html

type Literal = Int
type Clause  = [Literal]
type Problem = [Clause]
type Assignment = [Literal]

-- propagating the choice of the value of a literal to the rest of the problem, reducing the problem to a simpler one
propagate :: Literal -> Problem -> Problem
propagate l p = [ filter (/= negate l) c | c <- p, l `notElem` c ]

-- a simple backtracking search where we propagate the choice of the literal to the rest of the problem and check the smaller problem
solve :: Problem -> [Assignment]
solve []    = [[]]
solve (c:p) = do
  (l:c) <- [c]
  ([l:as | as <- solve (propagate l p)] ++ [negate l:as | as <- solve (propagate (negate l) (c:p))])

-- matching the Dafny end-to-end test
-- Main function to test the solver
main :: IO ()
main = do
  let problem1 = [[1, -2], [-1, 2], [2, 3], [-3]]
  let result1 = solve problem1

  if null result1
    then putStrLn "No solutions found"
    else putStrLn $ "Solutions: " ++ show result1

  let problem2 = [[1], [-1]] -- UNSAT (contradiction)
  let result2 = solve problem2

  if null result2
    then putStrLn "No solutions found"
    else putStrLn $ "Solutions: " ++ show result2