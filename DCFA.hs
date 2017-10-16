{-# LANGUAGE TupleSections #-}
-- Based on kcfa at matt.might.net, modified for call by name lambda calculus
module DCFA where

import Expr
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe (fromJust)
import qualified Control.Monad.State as St
import Debug.Trace
import GHC.TypeLits
import Data.Proxy

type State = (Clo, Store)
type Store = S.Set (Clo, Clo)
type Env = M.Map Var Clo
data Clo = Clo Expr Env
type Transitions = M.Map State (S.Set State)

-- Memoizations of single step and transitive closures, so if we had
-- subtypes we would have:
-- (M.Map State (S.Set State), M.Map State (S.Set (Lam, ...))
type Memo = (Transitions, Transitions)
type NEval = St.State Memo (S.Set State)

-- Lists expressions in bfs order
flatten :: Clo -> [Expr]
flatten c = bfs' [c] where
  bfs' [] = []
  bfs' (Clo exp env:cs) = exp:bfs' (cs ++ M.elems env)

instance Show Clo where
  show (Clo exp env) = "<" ++ show exp ++ ", " ++ show env ++ ">"

dcfa :: Int -> Expr -> Memo
dcfa d e = St.execState (eval (clo e M.empty, S.empty)) (M.empty, M.empty) where

  clo :: Expr -> Env -> Clo
  clo expr env = Clo expr env' where
    env' = M.fromList $ filter inscope $ M.assocs env
    inscope (v,c') = v `S.member` fvs expr

  -- Single step transition
  next :: State -> NEval
  next st@(Clo expr env, store) = do
    (single, close) <- St.get
    case M.lookup st single of
      Just vs -> return vs
      Nothing -> case expr of
        App l m n -> do 
          ls <- S.elems <$> eval (clo m env, store)
          let bs' = [(clo b (M.insert v (clo n env) env'), store'))
                    | (Clo (Lam l' v b) env', store') <- ls]
          let bs = S.fromList bs'
          (single, close) <- St.get
          St.put (M.insert st bs single, close)
          return bs
        Var l v -> return $ S.map (,store) cs where
          cs = fromJust $ do
            addr <- M.lookup v env
            cs <- M.lookup addr store
            (single, close) <- St.get
            St.put (M.insert st cs single, close)
            return cs

  -- Evaluation to value
  eval :: State -> NEval
  eval st@(expr, env, store) = do
    (single, close) <- St.get
    St.put (single, M.insertWith S.union st S.empty close)
    case M.lookup st close of
      Just vs -> return vs
      Nothing -> case expr of
        Lam l v b -> return $ S.singleton st
        _ -> do sts <- S.elems <$> next st
                vs <- S.unions <$> mapM eval sts
                (single, close) <- St.get
                St.put (single, M.insert st vs close)
                return vs
