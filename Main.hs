#!/usr/bin/env runhaskell
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Expr
import PDCFA
import Prelude hiding (exp, map)
import Data.Set
import Control.Monad (forM)
import System.Environment
import Control.Concurrent 
import System.IO

restrict :: Int -> Clo -> Clo
restrict 0 (Clo t e) = Clo t []
restrict i (Clo t e) = Clo t [(v, restrict (i-1) c) | (v,c) <- e]

type Options = (Restriction, TraceFunction Clo, TraceFunction Clo, Handle)

defaultOptions = (id, const $ return (), const $ return (), stdin)

parse :: Options -> [String] -> IO Options
parse (r, t, f, h) ("-k":k:args) = parse (restrict $ read k, t, f, h) args
parse (r, t, f, h) ("-t":"g":args) = parse (r, plotDSG, f, h) args
parse (r, t, f, h) ("-f":"g":args) = parse (r, t, plotDSG, h) args
parse (r, t, f, h) (file:args) = openFile file ReadMode >>= \h -> parse (r,t,f, h) args
parse opts [] = return opts

main = do
  (r, t, fin, h) <- parse defaultOptions =<< getArgs
  expr <- fmap (either (error.show) id . parseExpr "") $ hGetContents h
  (e, h, s) <- g t r expr
  fin e
  mapM_ print [ (c', c'') | (c'@(Clo (Var _ _) _), c''@(Clo (Lam _ _ _) _)) <- elems h ]
