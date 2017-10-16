#!/usr/bin/env runhaskell
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

--import DCFA
import Expr
import PDCFA
import Prelude hiding (exp, map)
import Data.Set
import qualified Data.Map as M
import Control.Monad (forM)
import System.Environment
import Control.Concurrent 
import System.IO
import KCFA

restrict :: Int -> Clo -> Clo
restrict 0 (Clo t e) = Clo t []
restrict i (Clo t e) = Clo t [(v, restrict (i-1) c) | (v,c) <- e]

type K = Int

data Options = Options {
  k :: K,
  restriction :: Restriction,
  trace :: TraceFunction Clo,
  final :: TraceFunction Clo,
  handle :: Handle
}

defaultOptions = Options 
  0
  id 
  (const $ return ()) 
  (const $ return ())
  stdin

parse :: Options -> [String] -> IO Options
parse ops ("-d":d:args) = parse (ops {restriction = restrict $ read d}) args
parse ops ("-k":k:args) = parse (ops {k = read k}) args
parse ops ("-t":"g":args) = parse (ops {trace = plotDSG}) args
parse ops ("-t":"s":args) = parse (ops {trace = print . size}) args
parse ops ("-f":"g":args) = parse (ops {final = plotDSG}) args
parse ops (file:args) = openFile file ReadMode >>= \h -> parse (ops {handle=h}) args
parse opts [] = return opts

main = do
  Options k r t fin h <- parse defaultOptions =<< getArgs
  expr <- fmap (either (error.show) id . parseExpr "") $ hGetContents h
  putStrLn "DCFA"
  (e, h, s) <- g t r expr
  fin e
  mapM_ print [ (c', c'') | (c'@(Clo (Var _ _) _), c''@(Clo (Lam _ _ _) _)) <- elems h ]
  putStrLn "KCFA"
  let (ts, vs) = kcfa k expr
  mapM_ print [ (c', vs) | ((c', _, _, _), c'') <- M.assocs vs, vs <- [v|(v,_,_,_)<-elems c'']]
  
