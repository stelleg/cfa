{-# LANGUAGE OverloadedStrings #-}

module PDCFA where
import Expr
import Data.Set hiding (foldr, filter)
import Data.Maybe
import Prelude hiding (map, exp, pred)
import Text.Parsec.Pos (newPos, sourceLine, sourceColumn)
import Debug.Trace
import Data.GraphViz.Types.Monadic
import Data.GraphViz.Attributes.Complete hiding (Lt, label, Label, EdgeType)
import Data.GraphViz.Attributes 
import Data.GraphViz.Commands
import Data.Text.Lazy (pack)

-- Adaptation of earl et al.
data Clo = Clo {exp :: Expr, env :: Env} deriving (Ord, Eq)
type Env = [(Var, Clo)]
type Edge a = (a, EdgeType, a)
data EdgeType = Push Clo | Pop Clo | Enter deriving (Ord, Eq, Show)
type Restriction = Clo -> Clo
type Conf = (Clo, [Clo], Set Clo)
type TraceFunction a = Set (Edge a) -> IO () 

-- Single Threaded Store PDCFA
type Store = Set Clo
type SingleStore = (Set (Edge Clo), Set (Clo, Clo), Store)

g :: TraceFunction Clo -> Restriction -> Expr -> IO SingleStore
g m r e = g' si where
  si = (singleton (Clo (Var (newPos "" 0 0) "main") [], Enter, Clo e []), empty, empty)
  g' ss@(e, h, s) = m e >> if ss == ss' then return ss else g' ss' where 
    ss' = (e', h', s') 
    push = fromList [ (c, Push$clo n env, clo m env) | (_, _, c@(Clo (App l m n) env)) <- elems e]
    enter = fromList [ (c, Enter, fjlu v env') | c'@(Clo _ env') <- elems s, 
                                                 (_, _, c@(Clo (Var l v) env)) <- elems e,
                                                 match c c'] 
    pop = fromList [ (c'', Pop arg, r$clo b$(v,arg):env) | (c, Push arg, c') <- elems e,
                                                           (cm', c''@(Clo (Lam l v b) env)) <- (c', c'):elems h,
                                                           cm' == c']
    s' = s `union` fromList [Clo v [(v',arg)] | 
                             (Clo (Lam l v' b) env, Pop arg, _) <- elems pop, 
                             v <- vars v' b]
    e' = e `union` push `union` enter `union` pop
    hs = fromList [(c', c') | (c,t,c') <- elems e]
    he = fromList [(c, c'') | (c, c') <- elems h, (c'_, c'') <- elems h, c' == c'_]
    he' = fromList [(c, c') | (c, Enter, c') <- elems e]
    hp = fromList [(c, c''') | (c, Push arg, c') <- elems e, 
                               (c'_, c''_) <- elems h,
                               (c'', Pop arg_, c''') <- elems e,
                               c'_==c', c''_==c'', arg==arg_]
    h' = hp `union` he `union` hs `union` he'
 
-- Store per Node PDCFA
type Arg = Clo
type Node = (Clo, Set Clo)
type DSG = (Set Node, Set Arg, Set (Edge Node), Node)
type EEdge = (Node, Node)
type ECG = (Set Node, Set EEdge)
type ΔDSG = (Set Node, Set (Edge Node))
type ΔECG = Set EEdge
type IDSG = (DSG, ECG, ΔDSG, ΔECG)

f :: TraceFunction Node -> Restriction -> Expr -> IO DSG
f m r e = fix ((empty, empty, empty, q0), (empty, empty), (singleton q0, empty), empty) where
  fix :: IDSG -> IO DSG
  fix a@(g@(_,_,e,_),ge,dg,dh) = m e >> if a == a' then return g else fix a' where a' = f' a
  f' :: IDSG -> IDSG
  f' (g, ge, dg, dh) = (g', ge', dg', dh' `difference` h) where
    (s,gam,e,s0) = g
    (_,h) = ge
    (ds, de) = dg
    (de0, dh0) = pairunions $ map sprout ds
    (de1, dh1) = pairunions $ map (addedge g ge) de
    (de2, dh2) = pairunions $ map (addempty g ge) dh
    s' = s `union` ds
    e' = e `union` de
    h' = h `union` dh
    de' = de0 `union` de1 `union` de2
    ds' = fromList [s' | (s,g,s') <- elems $ de']
    dh' = dh0 `union` dh1 `union` dh2
    g' = (s `union` ds, gam, e', q0)
    ge' = (s', h')
    dg' = (ds' `difference` s', de' `difference` e')
  q0 = (Clo e [], empty)
  pairunions ps = (unions as, unions bs) where (as,bs) = unzip$elems$ps
  
  addedge :: DSG -> ECG -> Edge Node -> (Set (Edge Node), Set EEdge)
  addedge (n,a,g,n0) g' (s, Push arg, q) = (de, dh) where
    de = fromList [(q', Pop arg, q'') | q'@(c',b') <- desc q g', 
                                        q'' <- elems$map cn$t (c',[arg],b')]
    dh = fromList [(s, q'') | q'@(c',b') <- desc q g',
                              q'' <- elems$map cn$t (c',[],b')]
  addedge (n,a,g,n0) g' (s'', Pop arg, q) = (empty, dh) where
    dh = fromList [(s,q) | s' <- pred s'' g', (s, Push arg, sg') <- elems g, sg' == s']
  addedge dsg@(n,a,g,n0) g' (s, Enter, s') = addempty dsg g' (s,s')
  
  addempty :: DSG -> ECG -> EEdge -> (Set (Edge Node), Set EEdge) 
  addempty (n,a,g,n0) g' (s'',s''') = (de, dh) where
    de = fromList [(s'''', Pop arg, q) | s' <- pred s'' g', 
                                         s''''@(c,b) <- desc s''' g',
                                         (s, Push arg, sg') <- elems g,
                                         s' == sg', 
                                         q <- elems$map cn$t (c,[arg],b)]
    dh = unions $ fmap fromList [
          [ (s, q) | s' <- pred s'' g', s''''@(c,b) <- desc s''' g',
                     (s, Push arg, sg') <- elems g, s' == sg',
                     q <- elems$map cn$t (c,[arg],b) ],
          [ (s', s''') | s' <- pred s'' g'],
          [ (s'', s'''') | s'''' <- desc s''' g'],
          [ (s', s'''') | s' <- pred s'' g', s'''' <- desc s''' g']]

  sprout :: Node -> (Set (Edge Node), Set EEdge)
  sprout conf@(c@(Clo exp env), bs) = case exp of 
    App l m n -> (fromList [(conf, Push (clo n env), (c',b)) | (c',_,b) <- elems $ t (c,[],bs)], empty)
    Var l v -> (fromList es, fromList hs) where
      (es, hs) = unzip [((conf, Enter, (c',b')), (conf,(c',b'))) | (c',_,b') <- elems $ t (c,[],bs) ]
    _ -> (empty, empty)
    
  desc :: Node -> ECG -> [Node]
  desc n (ns,es) = n:[n' | (n'', n') <- elems es, n'' == n]
  
  pred :: Node -> ECG -> [Node]
  pred n (ns,es) = n:[n' | (n', n'') <- elems es, n'' == n]

  t :: Conf -> Set Conf
  t (c@(Clo exp env), st, bs) = case exp of
    Var l v  -> fromList [ (fjlu v env',st,bs) | c'@(Clo _ env') <- elems bs, match c c' ]
    App l m n -> singleton (clo m env, clo n env:st, bs) 
    Lam l v b -> case st of 
      [] -> empty 
      arg:s' -> singleton (r$clo b$(v,arg):env, s', bs `union` vs) where
        vs = fromList [Clo v' [(v,arg)] | v' <- vars v b]

-- Utility functions
vars :: Var -> Expr -> [Expr]
vars v e = case e of
  Var l v' | v' == v -> [e]
           | otherwise -> [] 
  App l m n -> vars v m ++ vars v n
  Lam l v' b | v' == v -> [] 
             | otherwise -> vars v b

edgeify :: (Conf, Conf) -> Edge Node
edgeify ((c@(Clo exp env), st, bs), (c', st', bs')) = case exp of
  App l m n -> (q, Push (Clo n env), q')
  Var l v -> (q, Enter, q')
  Lam l v b -> (q, Pop (head st), q')
  where q = (c, bs)
        q' = (c', bs')

fjlu :: Ord k => k -> [(k,v)] -> v 
fjlu k l = fromJust $ lookup k l

clo :: Expr -> Env -> Clo
clo exp env = Clo exp $ filter (\(v, c) -> v `member` fvs exp) env

match :: Clo -> Clo -> Bool
match (Clo exp env) (Clo exp' env') = exp == exp' && all id (zipWith match (fmap snd env) (fmap snd env'))

fvs :: Expr -> Set Var
fvs (Var l v) = singleton v
fvs (App l m n) = fvs m `union` fvs n
fvs (Lam l v b) = fvs b `difference` singleton v

cn :: Conf -> Node
cn (c,s,b) = (c,b)


-- Plotting and pretty printing
instance Show Clo where
  show (Clo exp env) = "<" ++ show exp ++ ", " ++ show env ++ ">"

plotDSG es = showGraph "cfa.dot" dot where 
  dot = digraph (Str "CFA") $ do
    graphAttrs [textLabel "CFA"]
    sequence [node (ind$loc$exp c) [textLabel (pack$take 20$show$c)] | (c',t,c) <- elems es]
    sequence [edge (ind$loc$exp c) (ind$loc$exp c') [textLabel$pack$take 20$show t] | (c,t,c') <- elems es] 
  showGraph fname dg = do
    runGraphviz dg DotOutput ("/tmp/" ++ fname)
    runGraphvizCanvas' dg Xlib
  ind loc = sourceLine loc * 200 + sourceColumn loc

