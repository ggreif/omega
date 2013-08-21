-- Time-stamp: <2010-06-15 10:56:02 cklin>

module Front where

import Types
import Data.Char
import Data.List
import System.IO



{-



-}



{- frown :-( -}

data Stack__
    = Empty__
    | T_1_9__ Stack__ Ident
    | T_1_13__ Stack__
    | T_1_4__ Stack__
    | T_1_18__ Stack__ String
    | T_1_2__ Stack__ ([Program])
    | T_1_6__ Stack__ Program
    | T_1_17__ Stack__ ([String])
    | T_2_3__ Stack__
    | T_4_9__ Stack__ Ident
    | T_4_13__ Stack__
    | T_4_4__ Stack__
    | T_4_18__ Stack__ String
    | T_4_5__ Stack__ ([Program])
    | T_4_6__ Stack__ Program
    | T_4_17__ Stack__ ([String])
    | T_6_7__ Stack__
    | T_7_9__ Stack__ Ident
    | T_7_13__ Stack__
    | T_7_4__ Stack__
    | T_7_18__ Stack__ String
    | T_7_8__ Stack__ ([Program])
    | T_7_6__ Stack__ Program
    | T_7_17__ Stack__ ([String])
    | T_9_20__ Stack__ Ident
    | T_9_10__ Stack__ ([Ident])
    | T_10_11__ Stack__
    | T_11_51__ Stack__
    | T_11_72__ Stack__
    | T_11_69__ Stack__ Ident
    | T_11_70__ Stack__ String
    | T_11_71__ Stack__ Integer
    | T_11_55__ Stack__
    | T_11_61__ Stack__
    | T_11_12__ Stack__ Term
    | T_11_48__ Stack__ Term
    | T_11_67__ Stack__ Term
    | T_13_14__ Stack__ String
    | T_14_20__ Stack__ Ident
    | T_14_15__ Stack__ ([Ident])
    | T_15_22__ Stack__
    | T_15_16__ Stack__ ([Cons])
    | T_18_18__ Stack__ String
    | T_18_19__ Stack__ ([String])
    | T_20_20__ Stack__ Ident
    | T_20_21__ Stack__ ([Ident])
    | T_22_23__ Stack__
    | T_23_26__ Stack__ String
    | T_23_24__ Stack__ ([Cons])
    | T_24_25__ Stack__
    | T_26_27__ Stack__
    | T_27_41__ Stack__
    | T_27_39__ Stack__ Ident
    | T_27_34__ Stack__ String
    | T_27_28__ Stack__ Type
    | T_27_31__ Stack__ Type
    | T_27_36__ Stack__ Type
    | T_28_29__ Stack__
    | T_29_26__ Stack__ String
    | T_29_30__ Stack__ ([Cons])
    | T_31_32__ Stack__
    | T_32_41__ Stack__
    | T_32_39__ Stack__ Ident
    | T_32_34__ Stack__ String
    | T_32_33__ Stack__ Type
    | T_32_31__ Stack__ Type
    | T_32_36__ Stack__ Type
    | T_34_41__ Stack__
    | T_34_39__ Stack__ Ident
    | T_34_40__ Stack__ String
    | T_34_35__ Stack__ ([Type])
    | T_34_37__ Stack__ Type
    | T_37_41__ Stack__
    | T_37_39__ Stack__ Ident
    | T_37_40__ Stack__ String
    | T_37_38__ Stack__ ([Type])
    | T_37_37__ Stack__ Type
    | T_41_41__ Stack__
    | T_41_42__ Stack__
    | T_41_39__ Stack__ Ident
    | T_41_34__ Stack__ String
    | T_41_43__ Stack__ Type
    | T_41_31__ Stack__ Type
    | T_41_36__ Stack__ Type
    | T_43_44__ Stack__
    | T_43_47__ Stack__
    | T_44_41__ Stack__
    | T_44_39__ Stack__ Ident
    | T_44_34__ Stack__ String
    | T_44_45__ Stack__ Type
    | T_44_31__ Stack__ Type
    | T_44_36__ Stack__ Type
    | T_45_46__ Stack__
    | T_48_49__ Stack__
    | T_48_72__ Stack__
    | T_48_69__ Stack__ Ident
    | T_48_70__ Stack__ String
    | T_48_71__ Stack__ Integer
    | T_48_68__ Stack__ Term
    | T_49_51__ Stack__
    | T_49_72__ Stack__
    | T_49_69__ Stack__ Ident
    | T_49_70__ Stack__ String
    | T_49_71__ Stack__ Integer
    | T_49_55__ Stack__
    | T_49_61__ Stack__
    | T_49_50__ Stack__ Term
    | T_49_48__ Stack__ Term
    | T_49_67__ Stack__ Term
    | T_51_52__ Stack__ Ident
    | T_52_53__ Stack__
    | T_53_51__ Stack__
    | T_53_72__ Stack__
    | T_53_69__ Stack__ Ident
    | T_53_70__ Stack__ String
    | T_53_71__ Stack__ Integer
    | T_53_55__ Stack__
    | T_53_61__ Stack__
    | T_53_54__ Stack__ Term
    | T_53_48__ Stack__ Term
    | T_53_67__ Stack__ Term
    | T_55_51__ Stack__
    | T_55_72__ Stack__
    | T_55_69__ Stack__ Ident
    | T_55_70__ Stack__ String
    | T_55_71__ Stack__ Integer
    | T_55_55__ Stack__
    | T_55_61__ Stack__
    | T_55_56__ Stack__ Term
    | T_55_48__ Stack__ Term
    | T_55_67__ Stack__ Term
    | T_56_57__ Stack__
    | T_57_58__ Stack__
    | T_58_92__ Stack__
    | T_58_90__ Stack__ String
    | T_58_97__ Stack__ Integer
    | T_58_59__ Stack__ ([(Pat, Term)])
    | T_58_85__ Stack__ Pat
    | T_59_60__ Stack__
    | T_61_62__ Stack__
    | T_62_79__ Stack__ Ident
    | T_62_63__ Stack__ ([(Ident, Term)])
    | T_63_64__ Stack__
    | T_64_65__ Stack__
    | T_65_51__ Stack__
    | T_65_72__ Stack__
    | T_65_69__ Stack__ Ident
    | T_65_70__ Stack__ String
    | T_65_71__ Stack__ Integer
    | T_65_55__ Stack__
    | T_65_61__ Stack__
    | T_65_66__ Stack__ Term
    | T_65_48__ Stack__ Term
    | T_65_67__ Stack__ Term
    | T_72_51__ Stack__
    | T_72_72__ Stack__
    | T_72_73__ Stack__
    | T_72_69__ Stack__ Ident
    | T_72_70__ Stack__ String
    | T_72_71__ Stack__ Integer
    | T_72_55__ Stack__
    | T_72_61__ Stack__
    | T_72_74__ Stack__ Term
    | T_72_48__ Stack__ Term
    | T_72_67__ Stack__ Term
    | T_74_76__ Stack__
    | T_74_75__ Stack__
    | T_76_51__ Stack__
    | T_76_72__ Stack__
    | T_76_69__ Stack__ Ident
    | T_76_70__ Stack__ String
    | T_76_71__ Stack__ Integer
    | T_76_55__ Stack__
    | T_76_61__ Stack__
    | T_76_77__ Stack__ Term
    | T_76_48__ Stack__ Term
    | T_76_67__ Stack__ Term
    | T_77_78__ Stack__
    | T_79_20__ Stack__ Ident
    | T_79_80__ Stack__ ([Ident])
    | T_80_81__ Stack__
    | T_81_51__ Stack__
    | T_81_72__ Stack__
    | T_81_69__ Stack__ Ident
    | T_81_70__ Stack__ String
    | T_81_71__ Stack__ Integer
    | T_81_55__ Stack__
    | T_81_61__ Stack__
    | T_81_82__ Stack__ Term
    | T_81_48__ Stack__ Term
    | T_81_67__ Stack__ Term
    | T_82_83__ Stack__
    | T_83_79__ Stack__ Ident
    | T_83_84__ Stack__ ([(Ident, Term)])
    | T_85_86__ Stack__
    | T_86_51__ Stack__
    | T_86_72__ Stack__
    | T_86_69__ Stack__ Ident
    | T_86_70__ Stack__ String
    | T_86_71__ Stack__ Integer
    | T_86_55__ Stack__
    | T_86_61__ Stack__
    | T_86_87__ Stack__ Term
    | T_86_48__ Stack__ Term
    | T_86_67__ Stack__ Term
    | T_87_88__ Stack__
    | T_88_92__ Stack__
    | T_88_90__ Stack__ String
    | T_88_97__ Stack__ Integer
    | T_88_89__ Stack__ ([(Pat, Term)])
    | T_88_85__ Stack__ Pat
    | T_90_20__ Stack__ Ident
    | T_90_91__ Stack__ ([Ident])
    | T_92_93__ Stack__ Ident
    | T_93_94__ Stack__
    | T_94_95__ Stack__ Ident
    | T_95_96__ Stack__

data Nonterminal__ = Top__ ([Program])

top tr__ = parse_1__ tr__ Empty__ >>= (\ (Top__ v1) -> return (v1))

parse_1__ ts__@tr__@[] st__ = parse_2__ ts__ (T_1_2__ st__ ([]))
parse_1__ (LexVar v1 : tr__) st__ = parse_9__ tr__ (T_1_9__ st__ v1)
parse_1__ (LexData : tr__) st__ = parse_13__ tr__ (T_1_13__ st__)
parse_1__ (LexNext : tr__) st__ = parse_4__ tr__ (T_1_4__ st__)
parse_1__ (LexDoc v1 : tr__) st__ = parse_18__ tr__ (T_1_18__ st__ v1)
parse_1__ ts__ st__ = frown ts__

parse_2__ tr__@[] st__ = parse_3__ tr__ (T_2_3__ st__)
parse_2__ ts__ st__ = frown ts__

parse_3__ ts__ (T_2_3__ (T_1_2__ st__ v1)) = return (Top__ v1)

parse_4__ ts__@tr__@[] st__ = parse_5__ ts__ (T_4_5__ st__ ([]))
parse_4__ (LexVar v1 : tr__) st__ = parse_9__ tr__ (T_4_9__ st__ v1)
parse_4__ (LexData : tr__) st__ = parse_13__ tr__ (T_4_13__ st__)
parse_4__ (LexNext : tr__) st__ = parse_4__ tr__ (T_4_4__ st__)
parse_4__ (LexDoc v1 : tr__) st__ = parse_18__ tr__ (T_4_18__ st__ v1)
parse_4__ ts__ st__ = frown ts__

parse_5__ ts__ (T_4_5__ (T_1_4__ st__) p) = parse_2__ ts__ (T_1_2__ st__ p)
parse_5__ ts__ (T_4_5__ (T_4_4__ st__) p) = parse_5__ ts__ (T_4_5__ st__ p)
parse_5__ ts__ (T_4_5__ (T_7_4__ st__) p) = parse_8__ ts__ (T_7_8__ st__ p)

parse_6__ (LexNext : tr__) st__ = parse_7__ tr__ (T_6_7__ st__)
parse_6__ ts__ st__ = frown ts__

parse_7__ ts__@tr__@[] st__ = parse_8__ ts__ (T_7_8__ st__ ([]))
parse_7__ (LexVar v1 : tr__) st__ = parse_9__ tr__ (T_7_9__ st__ v1)
parse_7__ (LexData : tr__) st__ = parse_13__ tr__ (T_7_13__ st__)
parse_7__ (LexNext : tr__) st__ = parse_4__ tr__ (T_7_4__ st__)
parse_7__ (LexDoc v1 : tr__) st__ = parse_18__ tr__ (T_7_18__ st__ v1)
parse_7__ ts__ st__ = frown ts__

parse_8__ ts__ (T_7_8__ (T_6_7__ (T_1_6__ st__ d)) p)
    = parse_2__ ts__ (T_1_2__ st__ (d:p))
parse_8__ ts__ (T_7_8__ (T_6_7__ (T_4_6__ st__ d)) p)
    = parse_5__ ts__ (T_4_5__ st__ (d:p))
parse_8__ ts__ (T_7_8__ (T_6_7__ (T_7_6__ st__ d)) p)
    = parse_8__ ts__ (T_7_8__ st__ (d:p))

parse_9__ ts__@(LexDef : tr__) st__ = parse_10__ ts__ (T_9_10__ st__ ([]))
parse_9__ (LexVar v1 : tr__) st__ = parse_20__ tr__ (T_9_20__ st__ v1)
parse_9__ ts__ st__ = frown ts__

parse_10__ (LexDef : tr__) st__ = parse_11__ tr__ (T_10_11__ st__)
parse_10__ ts__ st__ = frown ts__

parse_11__ (LexLam : tr__) st__ = parse_51__ tr__ (T_11_51__ st__)
parse_11__ (LexParL : tr__) st__ = parse_72__ tr__ (T_11_72__ st__)
parse_11__ (LexVar v1 : tr__) st__ = parse_69__ tr__ (T_11_69__ st__ v1)
parse_11__ (LexCon v1 : tr__) st__ = parse_70__ tr__ (T_11_70__ st__ v1)
parse_11__ (LexInt v1 : tr__) st__ = parse_71__ tr__ (T_11_71__ st__ v1)
parse_11__ (LexCase : tr__) st__ = parse_55__ tr__ (T_11_55__ st__)
parse_11__ (LexLet : tr__) st__ = parse_61__ tr__ (T_11_61__ st__)
parse_11__ ts__ st__ = frown ts__

parse_12__ ts__ (T_11_12__ (T_10_11__ (T_9_10__ (T_1_9__ st__ v) ax)) t)
    = parse_6__ ts__ (T_1_6__ st__ (Value v (foldr Lam t ax)))
parse_12__ ts__ (T_11_12__ (T_10_11__ (T_9_10__ (T_4_9__ st__ v) ax)) t)
    = parse_6__ ts__ (T_4_6__ st__ (Value v (foldr Lam t ax)))
parse_12__ ts__ (T_11_12__ (T_10_11__ (T_9_10__ (T_7_9__ st__ v) ax)) t)
    = parse_6__ ts__ (T_7_6__ st__ (Value v (foldr Lam t ax)))

parse_13__ (LexCon v1 : tr__) st__ = parse_14__ tr__ (T_13_14__ st__ v1)
parse_13__ ts__ st__ = frown ts__

parse_14__ (LexVar v1 : tr__) st__ = parse_20__ tr__ (T_14_20__ st__ v1)
parse_14__ ts__ st__
    = case st__ of { st__ -> parse_15__ ts__ (T_14_15__ st__ ([])) }

parse_15__ (LexWhere : tr__) st__ = parse_22__ tr__ (T_15_22__ st__)
parse_15__ ts__@(LexNext : tr__) st__ = parse_16__ ts__ (T_15_16__ st__ ([]))
parse_15__ ts__ st__ = frown ts__

parse_16__ ts__ (T_15_16__ (T_14_15__ (T_13_14__ (T_1_13__ st__) c) ax) cx)
    = parse_6__ ts__ (T_1_6__ st__ (Decl (Data c ax) cx))
parse_16__ ts__ (T_15_16__ (T_14_15__ (T_13_14__ (T_4_13__ st__) c) ax) cx)
    = parse_6__ ts__ (T_4_6__ st__ (Decl (Data c ax) cx))
parse_16__ ts__ (T_15_16__ (T_14_15__ (T_13_14__ (T_7_13__ st__) c) ax) cx)
    = parse_6__ ts__ (T_7_6__ st__ (Decl (Data c ax) cx))

parse_17__ ts__ (T_1_17__ st__ doc) = parse_6__ ts__ (T_1_6__ st__ (Info doc))
parse_17__ ts__ (T_4_17__ st__ doc) = parse_6__ ts__ (T_4_6__ st__ (Info doc))
parse_17__ ts__ (T_7_17__ st__ doc) = parse_6__ ts__ (T_7_6__ st__ (Info doc))

parse_18__ ts__@(LexNext : tr__) (T_1_18__ st__ c)
    = parse_17__ ts__ (T_1_17__ st__ ([c]))
parse_18__ ts__@(LexNext : tr__) (T_4_18__ st__ c)
    = parse_17__ ts__ (T_4_17__ st__ ([c]))
parse_18__ ts__@(LexNext : tr__) (T_7_18__ st__ c)
    = parse_17__ ts__ (T_7_17__ st__ ([c]))
parse_18__ ts__@(LexNext : tr__) (T_18_18__ st__ c)
    = parse_19__ ts__ (T_18_19__ st__ ([c]))
parse_18__ (LexDoc v1 : tr__) st__ = parse_18__ tr__ (T_18_18__ st__ v1)
parse_18__ ts__ st__ = frown ts__

parse_19__ ts__ (T_18_19__ (T_1_18__ st__ c) cx)
    = parse_17__ ts__ (T_1_17__ st__ (c:cx))
parse_19__ ts__ (T_18_19__ (T_4_18__ st__ c) cx)
    = parse_17__ ts__ (T_4_17__ st__ (c:cx))
parse_19__ ts__ (T_18_19__ (T_7_18__ st__ c) cx)
    = parse_17__ ts__ (T_7_17__ st__ (c:cx))
parse_19__ ts__ (T_18_19__ (T_18_18__ st__ c) cx)
    = parse_19__ ts__ (T_18_19__ st__ (c:cx))

parse_20__ (LexVar v1 : tr__) st__ = parse_20__ tr__ (T_20_20__ st__ v1)
parse_20__ ts__ st__
    = case st__ of { st__ -> parse_21__ ts__ (T_20_21__ st__ ([])) }

parse_21__ ts__ (T_20_21__ (T_9_20__ st__ v) ax)
    = parse_10__ ts__ (T_9_10__ st__ (v:ax))
parse_21__ ts__ (T_20_21__ (T_14_20__ st__ v) ax)
    = parse_15__ ts__ (T_14_15__ st__ (v:ax))
parse_21__ ts__ (T_20_21__ (T_20_20__ st__ v) ax)
    = parse_21__ ts__ (T_20_21__ st__ (v:ax))
parse_21__ ts__ (T_20_21__ (T_79_20__ st__ v) ax)
    = parse_80__ ts__ (T_79_80__ st__ (v:ax))
parse_21__ ts__ (T_20_21__ (T_90_20__ st__ v) ax)
    = parse_91__ ts__ (T_90_91__ st__ (v:ax))

parse_22__ (LexBraL : tr__) st__ = parse_23__ tr__ (T_22_23__ st__)
parse_22__ ts__ st__ = frown ts__

parse_23__ (LexCon v1 : tr__) st__ = parse_26__ tr__ (T_23_26__ st__ v1)
parse_23__ ts__ st__ = frown ts__

parse_24__ (LexBraR : tr__) st__ = parse_25__ tr__ (T_24_25__ st__)
parse_24__ ts__ st__ = frown ts__

parse_25__ ts__ (T_24_25__ (T_23_24__ (T_22_23__ (T_15_22__ st__)) cx))
    = parse_16__ ts__ (T_15_16__ st__ cx)

parse_26__ (LexType : tr__) st__ = parse_27__ tr__ (T_26_27__ st__)
parse_26__ ts__ st__ = frown ts__

parse_27__ (LexParL : tr__) st__ = parse_41__ tr__ (T_27_41__ st__)
parse_27__ (LexVar v1 : tr__) st__ = parse_39__ tr__ (T_27_39__ st__ v1)
parse_27__ (LexCon v1 : tr__) st__ = parse_34__ tr__ (T_27_34__ st__ v1)
parse_27__ ts__ st__ = frown ts__

parse_28__ (LexSemi : tr__) st__ = parse_29__ tr__ (T_28_29__ st__)
parse_28__ ts__@(LexBraR : tr__) (T_27_28__ (T_26_27__ (T_23_26__ st__ c)) t)
    = parse_24__ ts__ (T_23_24__ st__ ([Cons c t]))
parse_28__ ts__@(LexBraR : tr__) (T_27_28__ (T_26_27__ (T_29_26__ st__ c)) t)
    = parse_30__ ts__ (T_29_30__ st__ ([Cons c t]))
parse_28__ ts__ st__ = frown ts__

parse_29__ (LexCon v1 : tr__) st__ = parse_26__ tr__ (T_29_26__ st__ v1)
parse_29__ ts__ st__ = frown ts__

parse_30__ ts__
    (T_29_30__ (T_28_29__ (T_27_28__ (T_26_27__ (T_23_26__ st__ c)) t)) cx)
    = parse_24__ ts__ (T_23_24__ st__ (Cons c t:cx))
parse_30__ ts__
    (T_29_30__ (T_28_29__ (T_27_28__ (T_26_27__ (T_29_26__ st__ c)) t)) cx)
    = parse_30__ ts__ (T_29_30__ st__ (Cons c t:cx))

parse_31__ (LexArr : tr__) st__ = parse_32__ tr__ (T_31_32__ st__)
parse_31__ ts__ st__
    = case st__ of {
          T_27_31__ st__ t -> parse_28__ ts__ (T_27_28__ st__ t);
          T_32_31__ st__ t -> parse_33__ ts__ (T_32_33__ st__ t);
          T_41_31__ st__ t -> parse_43__ ts__ (T_41_43__ st__ t);
          T_44_31__ st__ t -> parse_45__ ts__ (T_44_45__ st__ t) }

parse_32__ (LexParL : tr__) st__ = parse_41__ tr__ (T_32_41__ st__)
parse_32__ (LexVar v1 : tr__) st__ = parse_39__ tr__ (T_32_39__ st__ v1)
parse_32__ (LexCon v1 : tr__) st__ = parse_34__ tr__ (T_32_34__ st__ v1)
parse_32__ ts__ st__ = frown ts__

parse_33__ ts__ (T_32_33__ (T_31_32__ (T_27_31__ st__ t)) u)
    = parse_28__ ts__ (T_27_28__ st__ (arrType t u))
parse_33__ ts__ (T_32_33__ (T_31_32__ (T_32_31__ st__ t)) u)
    = parse_33__ ts__ (T_32_33__ st__ (arrType t u))
parse_33__ ts__ (T_32_33__ (T_31_32__ (T_41_31__ st__ t)) u)
    = parse_43__ ts__ (T_41_43__ st__ (arrType t u))
parse_33__ ts__ (T_32_33__ (T_31_32__ (T_44_31__ st__ t)) u)
    = parse_45__ ts__ (T_44_45__ st__ (arrType t u))

parse_34__ (LexParL : tr__) st__ = parse_41__ tr__ (T_34_41__ st__)
parse_34__ (LexVar v1 : tr__) st__ = parse_39__ tr__ (T_34_39__ st__ v1)
parse_34__ (LexCon v1 : tr__) st__ = parse_40__ tr__ (T_34_40__ st__ v1)
parse_34__ ts__ st__
    = case st__ of {
          T_27_34__ st__ c -> parse_36__ ts__ (T_27_36__ st__ (TyCon c []));
          T_32_34__ st__ c -> parse_36__ ts__ (T_32_36__ st__ (TyCon c []));
          T_41_34__ st__ c -> parse_36__ ts__ (T_41_36__ st__ (TyCon c []));
          T_44_34__ st__ c -> parse_36__ ts__ (T_44_36__ st__ (TyCon c [])) }

parse_35__ ts__ (T_34_35__ (T_27_34__ st__ c) ax)
    = parse_31__ ts__ (T_27_31__ st__ (TyCon c ax))
parse_35__ ts__ (T_34_35__ (T_32_34__ st__ c) ax)
    = parse_31__ ts__ (T_32_31__ st__ (TyCon c ax))
parse_35__ ts__ (T_34_35__ (T_41_34__ st__ c) ax)
    = parse_31__ ts__ (T_41_31__ st__ (TyCon c ax))
parse_35__ ts__ (T_34_35__ (T_44_34__ st__ c) ax)
    = parse_31__ ts__ (T_44_31__ st__ (TyCon c ax))

parse_36__ ts__ (T_27_36__ st__ t) = parse_31__ ts__ (T_27_31__ st__ t)
parse_36__ ts__ (T_32_36__ st__ t) = parse_31__ ts__ (T_32_31__ st__ t)
parse_36__ ts__ (T_41_36__ st__ t) = parse_31__ ts__ (T_41_31__ st__ t)
parse_36__ ts__ (T_44_36__ st__ t) = parse_31__ ts__ (T_44_31__ st__ t)

parse_37__ (LexParL : tr__) st__ = parse_41__ tr__ (T_37_41__ st__)
parse_37__ (LexVar v1 : tr__) st__ = parse_39__ tr__ (T_37_39__ st__ v1)
parse_37__ (LexCon v1 : tr__) st__ = parse_40__ tr__ (T_37_40__ st__ v1)
parse_37__ ts__ st__
    = case st__ of {
          T_34_37__ st__ t -> parse_35__ ts__ (T_34_35__ st__ ([t]));
          T_37_37__ st__ t -> parse_38__ ts__ (T_37_38__ st__ ([t])) }

parse_38__ ts__ (T_37_38__ (T_34_37__ st__ t) tx)
    = parse_35__ ts__ (T_34_35__ st__ (t:tx))
parse_38__ ts__ (T_37_38__ (T_37_37__ st__ t) tx)
    = parse_38__ ts__ (T_37_38__ st__ (t:tx))

parse_39__ ts__ (T_27_39__ st__ v) = parse_36__ ts__ (T_27_36__ st__ (TyVar v))
parse_39__ ts__ (T_32_39__ st__ v) = parse_36__ ts__ (T_32_36__ st__ (TyVar v))
parse_39__ ts__ (T_34_39__ st__ v) = parse_37__ ts__ (T_34_37__ st__ (TyVar v))
parse_39__ ts__ (T_37_39__ st__ v) = parse_37__ ts__ (T_37_37__ st__ (TyVar v))
parse_39__ ts__ (T_41_39__ st__ v) = parse_36__ ts__ (T_41_36__ st__ (TyVar v))
parse_39__ ts__ (T_44_39__ st__ v) = parse_36__ ts__ (T_44_36__ st__ (TyVar v))

parse_40__ ts__ (T_34_40__ st__ c)
    = parse_37__ ts__ (T_34_37__ st__ (TyCon c []))
parse_40__ ts__ (T_37_40__ st__ c)
    = parse_37__ ts__ (T_37_37__ st__ (TyCon c []))

parse_41__ (LexParL : tr__) st__ = parse_41__ tr__ (T_41_41__ st__)
parse_41__ (LexParR : tr__) st__ = parse_42__ tr__ (T_41_42__ st__)
parse_41__ (LexVar v1 : tr__) st__ = parse_39__ tr__ (T_41_39__ st__ v1)
parse_41__ (LexCon v1 : tr__) st__ = parse_34__ tr__ (T_41_34__ st__ v1)
parse_41__ ts__ st__ = frown ts__

parse_42__ ts__ (T_41_42__ (T_27_41__ st__))
    = parse_36__ ts__ (T_27_36__ st__ (TyCon "()" []))
parse_42__ ts__ (T_41_42__ (T_32_41__ st__))
    = parse_36__ ts__ (T_32_36__ st__ (TyCon "()" []))
parse_42__ ts__ (T_41_42__ (T_34_41__ st__))
    = parse_37__ ts__ (T_34_37__ st__ (TyCon "()" []))
parse_42__ ts__ (T_41_42__ (T_37_41__ st__))
    = parse_37__ ts__ (T_37_37__ st__ (TyCon "()" []))
parse_42__ ts__ (T_41_42__ (T_41_41__ st__))
    = parse_36__ ts__ (T_41_36__ st__ (TyCon "()" []))
parse_42__ ts__ (T_41_42__ (T_44_41__ st__))
    = parse_36__ ts__ (T_44_36__ st__ (TyCon "()" []))

parse_43__ (LexComa : tr__) st__ = parse_44__ tr__ (T_43_44__ st__)
parse_43__ (LexParR : tr__) st__ = parse_47__ tr__ (T_43_47__ st__)
parse_43__ ts__ st__ = frown ts__

parse_44__ (LexParL : tr__) st__ = parse_41__ tr__ (T_44_41__ st__)
parse_44__ (LexVar v1 : tr__) st__ = parse_39__ tr__ (T_44_39__ st__ v1)
parse_44__ (LexCon v1 : tr__) st__ = parse_34__ tr__ (T_44_34__ st__ v1)
parse_44__ ts__ st__ = frown ts__

parse_45__ (LexParR : tr__) st__ = parse_46__ tr__ (T_45_46__ st__)
parse_45__ ts__ st__ = frown ts__

parse_46__ ts__
    (T_45_46__ (T_44_45__ (T_43_44__ (T_41_43__ (T_27_41__ st__) u)) v))
    = parse_36__ ts__ (T_27_36__ st__ (TyCon "," [u, v]))
parse_46__ ts__
    (T_45_46__ (T_44_45__ (T_43_44__ (T_41_43__ (T_32_41__ st__) u)) v))
    = parse_36__ ts__ (T_32_36__ st__ (TyCon "," [u, v]))
parse_46__ ts__
    (T_45_46__ (T_44_45__ (T_43_44__ (T_41_43__ (T_34_41__ st__) u)) v))
    = parse_37__ ts__ (T_34_37__ st__ (TyCon "," [u, v]))
parse_46__ ts__
    (T_45_46__ (T_44_45__ (T_43_44__ (T_41_43__ (T_37_41__ st__) u)) v))
    = parse_37__ ts__ (T_37_37__ st__ (TyCon "," [u, v]))
parse_46__ ts__
    (T_45_46__ (T_44_45__ (T_43_44__ (T_41_43__ (T_41_41__ st__) u)) v))
    = parse_36__ ts__ (T_41_36__ st__ (TyCon "," [u, v]))
parse_46__ ts__
    (T_45_46__ (T_44_45__ (T_43_44__ (T_41_43__ (T_44_41__ st__) u)) v))
    = parse_36__ ts__ (T_44_36__ st__ (TyCon "," [u, v]))

parse_47__ ts__ (T_43_47__ (T_41_43__ (T_27_41__ st__) t))
    = parse_36__ ts__ (T_27_36__ st__ t)
parse_47__ ts__ (T_43_47__ (T_41_43__ (T_32_41__ st__) t))
    = parse_36__ ts__ (T_32_36__ st__ t)
parse_47__ ts__ (T_43_47__ (T_41_43__ (T_34_41__ st__) t))
    = parse_37__ ts__ (T_34_37__ st__ t)
parse_47__ ts__ (T_43_47__ (T_41_43__ (T_37_41__ st__) t))
    = parse_37__ ts__ (T_37_37__ st__ t)
parse_47__ ts__ (T_43_47__ (T_41_43__ (T_41_41__ st__) t))
    = parse_36__ ts__ (T_41_36__ st__ t)
parse_47__ ts__ (T_43_47__ (T_41_43__ (T_44_41__ st__) t))
    = parse_36__ ts__ (T_44_36__ st__ t)

parse_48__ (LexOp : tr__) st__ = parse_49__ tr__ (T_48_49__ st__)
parse_48__ (LexParL : tr__) st__ = parse_72__ tr__ (T_48_72__ st__)
parse_48__ (LexVar v1 : tr__) st__ = parse_69__ tr__ (T_48_69__ st__ v1)
parse_48__ (LexCon v1 : tr__) st__ = parse_70__ tr__ (T_48_70__ st__ v1)
parse_48__ (LexInt v1 : tr__) st__ = parse_71__ tr__ (T_48_71__ st__ v1)
parse_48__ ts__ st__
    = case st__ of {
          T_11_48__ st__ t -> parse_12__ ts__ (T_11_12__ st__ t);
          T_49_48__ st__ t -> parse_50__ ts__ (T_49_50__ st__ t);
          T_53_48__ st__ t -> parse_54__ ts__ (T_53_54__ st__ t);
          T_55_48__ st__ t -> parse_56__ ts__ (T_55_56__ st__ t);
          T_65_48__ st__ t -> parse_66__ ts__ (T_65_66__ st__ t);
          T_72_48__ st__ t -> parse_74__ ts__ (T_72_74__ st__ t);
          T_76_48__ st__ t -> parse_77__ ts__ (T_76_77__ st__ t);
          T_81_48__ st__ t -> parse_82__ ts__ (T_81_82__ st__ t);
          T_86_48__ st__ t -> parse_87__ ts__ (T_86_87__ st__ t) }

parse_49__ (LexLam : tr__) st__ = parse_51__ tr__ (T_49_51__ st__)
parse_49__ (LexParL : tr__) st__ = parse_72__ tr__ (T_49_72__ st__)
parse_49__ (LexVar v1 : tr__) st__ = parse_69__ tr__ (T_49_69__ st__ v1)
parse_49__ (LexCon v1 : tr__) st__ = parse_70__ tr__ (T_49_70__ st__ v1)
parse_49__ (LexInt v1 : tr__) st__ = parse_71__ tr__ (T_49_71__ st__ v1)
parse_49__ (LexCase : tr__) st__ = parse_55__ tr__ (T_49_55__ st__)
parse_49__ (LexLet : tr__) st__ = parse_61__ tr__ (T_49_61__ st__)
parse_49__ ts__ st__ = frown ts__

parse_50__ ts__ (T_49_50__ (T_48_49__ (T_11_48__ st__ t)) u)
    = parse_12__ ts__ (T_11_12__ st__ (App (App (Var "+") t) u))
parse_50__ ts__ (T_49_50__ (T_48_49__ (T_49_48__ st__ t)) u)
    = parse_50__ ts__ (T_49_50__ st__ (App (App (Var "+") t) u))
parse_50__ ts__ (T_49_50__ (T_48_49__ (T_53_48__ st__ t)) u)
    = parse_54__ ts__ (T_53_54__ st__ (App (App (Var "+") t) u))
parse_50__ ts__ (T_49_50__ (T_48_49__ (T_55_48__ st__ t)) u)
    = parse_56__ ts__ (T_55_56__ st__ (App (App (Var "+") t) u))
parse_50__ ts__ (T_49_50__ (T_48_49__ (T_65_48__ st__ t)) u)
    = parse_66__ ts__ (T_65_66__ st__ (App (App (Var "+") t) u))
parse_50__ ts__ (T_49_50__ (T_48_49__ (T_72_48__ st__ t)) u)
    = parse_74__ ts__ (T_72_74__ st__ (App (App (Var "+") t) u))
parse_50__ ts__ (T_49_50__ (T_48_49__ (T_76_48__ st__ t)) u)
    = parse_77__ ts__ (T_76_77__ st__ (App (App (Var "+") t) u))
parse_50__ ts__ (T_49_50__ (T_48_49__ (T_81_48__ st__ t)) u)
    = parse_82__ ts__ (T_81_82__ st__ (App (App (Var "+") t) u))
parse_50__ ts__ (T_49_50__ (T_48_49__ (T_86_48__ st__ t)) u)
    = parse_87__ ts__ (T_86_87__ st__ (App (App (Var "+") t) u))

parse_51__ (LexVar v1 : tr__) st__ = parse_52__ tr__ (T_51_52__ st__ v1)
parse_51__ ts__ st__ = frown ts__

parse_52__ (LexArr : tr__) st__ = parse_53__ tr__ (T_52_53__ st__)
parse_52__ ts__ st__ = frown ts__

parse_53__ (LexLam : tr__) st__ = parse_51__ tr__ (T_53_51__ st__)
parse_53__ (LexParL : tr__) st__ = parse_72__ tr__ (T_53_72__ st__)
parse_53__ (LexVar v1 : tr__) st__ = parse_69__ tr__ (T_53_69__ st__ v1)
parse_53__ (LexCon v1 : tr__) st__ = parse_70__ tr__ (T_53_70__ st__ v1)
parse_53__ (LexInt v1 : tr__) st__ = parse_71__ tr__ (T_53_71__ st__ v1)
parse_53__ (LexCase : tr__) st__ = parse_55__ tr__ (T_53_55__ st__)
parse_53__ (LexLet : tr__) st__ = parse_61__ tr__ (T_53_61__ st__)
parse_53__ ts__ st__ = frown ts__

parse_54__ ts__ (T_53_54__ (T_52_53__ (T_51_52__ (T_11_51__ st__) a)) u)
    = parse_12__ ts__ (T_11_12__ st__ (Lam a u))
parse_54__ ts__ (T_53_54__ (T_52_53__ (T_51_52__ (T_49_51__ st__) a)) u)
    = parse_50__ ts__ (T_49_50__ st__ (Lam a u))
parse_54__ ts__ (T_53_54__ (T_52_53__ (T_51_52__ (T_53_51__ st__) a)) u)
    = parse_54__ ts__ (T_53_54__ st__ (Lam a u))
parse_54__ ts__ (T_53_54__ (T_52_53__ (T_51_52__ (T_55_51__ st__) a)) u)
    = parse_56__ ts__ (T_55_56__ st__ (Lam a u))
parse_54__ ts__ (T_53_54__ (T_52_53__ (T_51_52__ (T_65_51__ st__) a)) u)
    = parse_66__ ts__ (T_65_66__ st__ (Lam a u))
parse_54__ ts__ (T_53_54__ (T_52_53__ (T_51_52__ (T_72_51__ st__) a)) u)
    = parse_74__ ts__ (T_72_74__ st__ (Lam a u))
parse_54__ ts__ (T_53_54__ (T_52_53__ (T_51_52__ (T_76_51__ st__) a)) u)
    = parse_77__ ts__ (T_76_77__ st__ (Lam a u))
parse_54__ ts__ (T_53_54__ (T_52_53__ (T_51_52__ (T_81_51__ st__) a)) u)
    = parse_82__ ts__ (T_81_82__ st__ (Lam a u))
parse_54__ ts__ (T_53_54__ (T_52_53__ (T_51_52__ (T_86_51__ st__) a)) u)
    = parse_87__ ts__ (T_86_87__ st__ (Lam a u))

parse_55__ (LexLam : tr__) st__ = parse_51__ tr__ (T_55_51__ st__)
parse_55__ (LexParL : tr__) st__ = parse_72__ tr__ (T_55_72__ st__)
parse_55__ (LexVar v1 : tr__) st__ = parse_69__ tr__ (T_55_69__ st__ v1)
parse_55__ (LexCon v1 : tr__) st__ = parse_70__ tr__ (T_55_70__ st__ v1)
parse_55__ (LexInt v1 : tr__) st__ = parse_71__ tr__ (T_55_71__ st__ v1)
parse_55__ (LexCase : tr__) st__ = parse_55__ tr__ (T_55_55__ st__)
parse_55__ (LexLet : tr__) st__ = parse_61__ tr__ (T_55_61__ st__)
parse_55__ ts__ st__ = frown ts__

parse_56__ (LexOf : tr__) st__ = parse_57__ tr__ (T_56_57__ st__)
parse_56__ ts__ st__ = frown ts__

parse_57__ (LexBraL : tr__) st__ = parse_58__ tr__ (T_57_58__ st__)
parse_57__ ts__ st__ = frown ts__

parse_58__ (LexParL : tr__) st__ = parse_92__ tr__ (T_58_92__ st__)
parse_58__ (LexCon v1 : tr__) st__ = parse_90__ tr__ (T_58_90__ st__ v1)
parse_58__ (LexInt v1 : tr__) st__ = parse_97__ tr__ (T_58_97__ st__ v1)
parse_58__ ts__ st__ = frown ts__

parse_59__ (LexBraR : tr__) st__ = parse_60__ tr__ (T_59_60__ st__)
parse_59__ ts__ st__ = frown ts__

parse_60__ ts__
    (T_59_60__
         (T_58_59__ (T_57_58__ (T_56_57__ (T_55_56__ (T_11_55__ st__) c))) bx))
    = parse_12__ ts__ (T_11_12__ st__ (Case c bx))
parse_60__ ts__
    (T_59_60__
         (T_58_59__ (T_57_58__ (T_56_57__ (T_55_56__ (T_49_55__ st__) c))) bx))
    = parse_50__ ts__ (T_49_50__ st__ (Case c bx))
parse_60__ ts__
    (T_59_60__
         (T_58_59__ (T_57_58__ (T_56_57__ (T_55_56__ (T_53_55__ st__) c))) bx))
    = parse_54__ ts__ (T_53_54__ st__ (Case c bx))
parse_60__ ts__
    (T_59_60__
         (T_58_59__ (T_57_58__ (T_56_57__ (T_55_56__ (T_55_55__ st__) c))) bx))
    = parse_56__ ts__ (T_55_56__ st__ (Case c bx))
parse_60__ ts__
    (T_59_60__
         (T_58_59__ (T_57_58__ (T_56_57__ (T_55_56__ (T_65_55__ st__) c))) bx))
    = parse_66__ ts__ (T_65_66__ st__ (Case c bx))
parse_60__ ts__
    (T_59_60__
         (T_58_59__ (T_57_58__ (T_56_57__ (T_55_56__ (T_72_55__ st__) c))) bx))
    = parse_74__ ts__ (T_72_74__ st__ (Case c bx))
parse_60__ ts__
    (T_59_60__
         (T_58_59__ (T_57_58__ (T_56_57__ (T_55_56__ (T_76_55__ st__) c))) bx))
    = parse_77__ ts__ (T_76_77__ st__ (Case c bx))
parse_60__ ts__
    (T_59_60__
         (T_58_59__ (T_57_58__ (T_56_57__ (T_55_56__ (T_81_55__ st__) c))) bx))
    = parse_82__ ts__ (T_81_82__ st__ (Case c bx))
parse_60__ ts__
    (T_59_60__
         (T_58_59__ (T_57_58__ (T_56_57__ (T_55_56__ (T_86_55__ st__) c))) bx))
    = parse_87__ ts__ (T_86_87__ st__ (Case c bx))

parse_61__ (LexBraL : tr__) st__ = parse_62__ tr__ (T_61_62__ st__)
parse_61__ ts__ st__ = frown ts__

parse_62__ (LexVar v1 : tr__) st__ = parse_79__ tr__ (T_62_79__ st__ v1)
parse_62__ ts__ st__ = frown ts__

parse_63__ (LexBraR : tr__) st__ = parse_64__ tr__ (T_63_64__ st__)
parse_63__ ts__ st__ = frown ts__

parse_64__ (LexIn : tr__) st__ = parse_65__ tr__ (T_64_65__ st__)
parse_64__ ts__ st__ = frown ts__

parse_65__ (LexLam : tr__) st__ = parse_51__ tr__ (T_65_51__ st__)
parse_65__ (LexParL : tr__) st__ = parse_72__ tr__ (T_65_72__ st__)
parse_65__ (LexVar v1 : tr__) st__ = parse_69__ tr__ (T_65_69__ st__ v1)
parse_65__ (LexCon v1 : tr__) st__ = parse_70__ tr__ (T_65_70__ st__ v1)
parse_65__ (LexInt v1 : tr__) st__ = parse_71__ tr__ (T_65_71__ st__ v1)
parse_65__ (LexCase : tr__) st__ = parse_55__ tr__ (T_65_55__ st__)
parse_65__ (LexLet : tr__) st__ = parse_61__ tr__ (T_65_61__ st__)
parse_65__ ts__ st__ = frown ts__

parse_66__ ts__
    (T_65_66__
             (T_64_65__ (T_63_64__ (T_62_63__ (T_61_62__ (T_11_61__ st__)) dx)))
         t) = parse_12__ ts__ (T_11_12__ st__ (Let dx t))
parse_66__ ts__
    (T_65_66__
             (T_64_65__ (T_63_64__ (T_62_63__ (T_61_62__ (T_49_61__ st__)) dx)))
         t) = parse_50__ ts__ (T_49_50__ st__ (Let dx t))
parse_66__ ts__
    (T_65_66__
             (T_64_65__ (T_63_64__ (T_62_63__ (T_61_62__ (T_53_61__ st__)) dx)))
         t) = parse_54__ ts__ (T_53_54__ st__ (Let dx t))
parse_66__ ts__
    (T_65_66__
             (T_64_65__ (T_63_64__ (T_62_63__ (T_61_62__ (T_55_61__ st__)) dx)))
         t) = parse_56__ ts__ (T_55_56__ st__ (Let dx t))
parse_66__ ts__
    (T_65_66__
             (T_64_65__ (T_63_64__ (T_62_63__ (T_61_62__ (T_65_61__ st__)) dx)))
         t) = parse_66__ ts__ (T_65_66__ st__ (Let dx t))
parse_66__ ts__
    (T_65_66__
             (T_64_65__ (T_63_64__ (T_62_63__ (T_61_62__ (T_72_61__ st__)) dx)))
         t) = parse_74__ ts__ (T_72_74__ st__ (Let dx t))
parse_66__ ts__
    (T_65_66__
             (T_64_65__ (T_63_64__ (T_62_63__ (T_61_62__ (T_76_61__ st__)) dx)))
         t) = parse_77__ ts__ (T_76_77__ st__ (Let dx t))
parse_66__ ts__
    (T_65_66__
             (T_64_65__ (T_63_64__ (T_62_63__ (T_61_62__ (T_81_61__ st__)) dx)))
         t) = parse_82__ ts__ (T_81_82__ st__ (Let dx t))
parse_66__ ts__
    (T_65_66__
             (T_64_65__ (T_63_64__ (T_62_63__ (T_61_62__ (T_86_61__ st__)) dx)))
         t) = parse_87__ ts__ (T_86_87__ st__ (Let dx t))

parse_67__ ts__ (T_11_67__ st__ t) = parse_48__ ts__ (T_11_48__ st__ t)
parse_67__ ts__ (T_49_67__ st__ t) = parse_48__ ts__ (T_49_48__ st__ t)
parse_67__ ts__ (T_53_67__ st__ t) = parse_48__ ts__ (T_53_48__ st__ t)
parse_67__ ts__ (T_55_67__ st__ t) = parse_48__ ts__ (T_55_48__ st__ t)
parse_67__ ts__ (T_65_67__ st__ t) = parse_48__ ts__ (T_65_48__ st__ t)
parse_67__ ts__ (T_72_67__ st__ t) = parse_48__ ts__ (T_72_48__ st__ t)
parse_67__ ts__ (T_76_67__ st__ t) = parse_48__ ts__ (T_76_48__ st__ t)
parse_67__ ts__ (T_81_67__ st__ t) = parse_48__ ts__ (T_81_48__ st__ t)
parse_67__ ts__ (T_86_67__ st__ t) = parse_48__ ts__ (T_86_48__ st__ t)

parse_68__ ts__ (T_48_68__ (T_11_48__ st__ t) u)
    = parse_48__ ts__ (T_11_48__ st__ (App t u))
parse_68__ ts__ (T_48_68__ (T_49_48__ st__ t) u)
    = parse_48__ ts__ (T_49_48__ st__ (App t u))
parse_68__ ts__ (T_48_68__ (T_53_48__ st__ t) u)
    = parse_48__ ts__ (T_53_48__ st__ (App t u))
parse_68__ ts__ (T_48_68__ (T_55_48__ st__ t) u)
    = parse_48__ ts__ (T_55_48__ st__ (App t u))
parse_68__ ts__ (T_48_68__ (T_65_48__ st__ t) u)
    = parse_48__ ts__ (T_65_48__ st__ (App t u))
parse_68__ ts__ (T_48_68__ (T_72_48__ st__ t) u)
    = parse_48__ ts__ (T_72_48__ st__ (App t u))
parse_68__ ts__ (T_48_68__ (T_76_48__ st__ t) u)
    = parse_48__ ts__ (T_76_48__ st__ (App t u))
parse_68__ ts__ (T_48_68__ (T_81_48__ st__ t) u)
    = parse_48__ ts__ (T_81_48__ st__ (App t u))
parse_68__ ts__ (T_48_68__ (T_86_48__ st__ t) u)
    = parse_48__ ts__ (T_86_48__ st__ (App t u))

parse_69__ ts__ (T_11_69__ st__ v) = parse_67__ ts__ (T_11_67__ st__ (Var v))
parse_69__ ts__ (T_48_69__ st__ v) = parse_68__ ts__ (T_48_68__ st__ (Var v))
parse_69__ ts__ (T_49_69__ st__ v) = parse_67__ ts__ (T_49_67__ st__ (Var v))
parse_69__ ts__ (T_53_69__ st__ v) = parse_67__ ts__ (T_53_67__ st__ (Var v))
parse_69__ ts__ (T_55_69__ st__ v) = parse_67__ ts__ (T_55_67__ st__ (Var v))
parse_69__ ts__ (T_65_69__ st__ v) = parse_67__ ts__ (T_65_67__ st__ (Var v))
parse_69__ ts__ (T_72_69__ st__ v) = parse_67__ ts__ (T_72_67__ st__ (Var v))
parse_69__ ts__ (T_76_69__ st__ v) = parse_67__ ts__ (T_76_67__ st__ (Var v))
parse_69__ ts__ (T_81_69__ st__ v) = parse_67__ ts__ (T_81_67__ st__ (Var v))
parse_69__ ts__ (T_86_69__ st__ v) = parse_67__ ts__ (T_86_67__ st__ (Var v))

parse_70__ ts__ (T_11_70__ st__ c) = parse_67__ ts__ (T_11_67__ st__ (Con c))
parse_70__ ts__ (T_48_70__ st__ c) = parse_68__ ts__ (T_48_68__ st__ (Con c))
parse_70__ ts__ (T_49_70__ st__ c) = parse_67__ ts__ (T_49_67__ st__ (Con c))
parse_70__ ts__ (T_53_70__ st__ c) = parse_67__ ts__ (T_53_67__ st__ (Con c))
parse_70__ ts__ (T_55_70__ st__ c) = parse_67__ ts__ (T_55_67__ st__ (Con c))
parse_70__ ts__ (T_65_70__ st__ c) = parse_67__ ts__ (T_65_67__ st__ (Con c))
parse_70__ ts__ (T_72_70__ st__ c) = parse_67__ ts__ (T_72_67__ st__ (Con c))
parse_70__ ts__ (T_76_70__ st__ c) = parse_67__ ts__ (T_76_67__ st__ (Con c))
parse_70__ ts__ (T_81_70__ st__ c) = parse_67__ ts__ (T_81_67__ st__ (Con c))
parse_70__ ts__ (T_86_70__ st__ c) = parse_67__ ts__ (T_86_67__ st__ (Con c))

parse_71__ ts__ (T_11_71__ st__ i) = parse_67__ ts__ (T_11_67__ st__ (Int i))
parse_71__ ts__ (T_48_71__ st__ i) = parse_68__ ts__ (T_48_68__ st__ (Int i))
parse_71__ ts__ (T_49_71__ st__ i) = parse_67__ ts__ (T_49_67__ st__ (Int i))
parse_71__ ts__ (T_53_71__ st__ i) = parse_67__ ts__ (T_53_67__ st__ (Int i))
parse_71__ ts__ (T_55_71__ st__ i) = parse_67__ ts__ (T_55_67__ st__ (Int i))
parse_71__ ts__ (T_65_71__ st__ i) = parse_67__ ts__ (T_65_67__ st__ (Int i))
parse_71__ ts__ (T_72_71__ st__ i) = parse_67__ ts__ (T_72_67__ st__ (Int i))
parse_71__ ts__ (T_76_71__ st__ i) = parse_67__ ts__ (T_76_67__ st__ (Int i))
parse_71__ ts__ (T_81_71__ st__ i) = parse_67__ ts__ (T_81_67__ st__ (Int i))
parse_71__ ts__ (T_86_71__ st__ i) = parse_67__ ts__ (T_86_67__ st__ (Int i))

parse_72__ (LexLam : tr__) st__ = parse_51__ tr__ (T_72_51__ st__)
parse_72__ (LexParL : tr__) st__ = parse_72__ tr__ (T_72_72__ st__)
parse_72__ (LexParR : tr__) st__ = parse_73__ tr__ (T_72_73__ st__)
parse_72__ (LexVar v1 : tr__) st__ = parse_69__ tr__ (T_72_69__ st__ v1)
parse_72__ (LexCon v1 : tr__) st__ = parse_70__ tr__ (T_72_70__ st__ v1)
parse_72__ (LexInt v1 : tr__) st__ = parse_71__ tr__ (T_72_71__ st__ v1)
parse_72__ (LexCase : tr__) st__ = parse_55__ tr__ (T_72_55__ st__)
parse_72__ (LexLet : tr__) st__ = parse_61__ tr__ (T_72_61__ st__)
parse_72__ ts__ st__ = frown ts__

parse_73__ ts__ (T_72_73__ (T_11_72__ st__))
    = parse_67__ ts__ (T_11_67__ st__ (Con "()"))
parse_73__ ts__ (T_72_73__ (T_48_72__ st__))
    = parse_68__ ts__ (T_48_68__ st__ (Con "()"))
parse_73__ ts__ (T_72_73__ (T_49_72__ st__))
    = parse_67__ ts__ (T_49_67__ st__ (Con "()"))
parse_73__ ts__ (T_72_73__ (T_53_72__ st__))
    = parse_67__ ts__ (T_53_67__ st__ (Con "()"))
parse_73__ ts__ (T_72_73__ (T_55_72__ st__))
    = parse_67__ ts__ (T_55_67__ st__ (Con "()"))
parse_73__ ts__ (T_72_73__ (T_65_72__ st__))
    = parse_67__ ts__ (T_65_67__ st__ (Con "()"))
parse_73__ ts__ (T_72_73__ (T_72_72__ st__))
    = parse_67__ ts__ (T_72_67__ st__ (Con "()"))
parse_73__ ts__ (T_72_73__ (T_76_72__ st__))
    = parse_67__ ts__ (T_76_67__ st__ (Con "()"))
parse_73__ ts__ (T_72_73__ (T_81_72__ st__))
    = parse_67__ ts__ (T_81_67__ st__ (Con "()"))
parse_73__ ts__ (T_72_73__ (T_86_72__ st__))
    = parse_67__ ts__ (T_86_67__ st__ (Con "()"))

parse_74__ (LexComa : tr__) st__ = parse_76__ tr__ (T_74_76__ st__)
parse_74__ (LexParR : tr__) st__ = parse_75__ tr__ (T_74_75__ st__)
parse_74__ ts__ st__ = frown ts__

parse_75__ ts__ (T_74_75__ (T_72_74__ (T_11_72__ st__) t))
    = parse_67__ ts__ (T_11_67__ st__ t)
parse_75__ ts__ (T_74_75__ (T_72_74__ (T_48_72__ st__) t))
    = parse_68__ ts__ (T_48_68__ st__ t)
parse_75__ ts__ (T_74_75__ (T_72_74__ (T_49_72__ st__) t))
    = parse_67__ ts__ (T_49_67__ st__ t)
parse_75__ ts__ (T_74_75__ (T_72_74__ (T_53_72__ st__) t))
    = parse_67__ ts__ (T_53_67__ st__ t)
parse_75__ ts__ (T_74_75__ (T_72_74__ (T_55_72__ st__) t))
    = parse_67__ ts__ (T_55_67__ st__ t)
parse_75__ ts__ (T_74_75__ (T_72_74__ (T_65_72__ st__) t))
    = parse_67__ ts__ (T_65_67__ st__ t)
parse_75__ ts__ (T_74_75__ (T_72_74__ (T_72_72__ st__) t))
    = parse_67__ ts__ (T_72_67__ st__ t)
parse_75__ ts__ (T_74_75__ (T_72_74__ (T_76_72__ st__) t))
    = parse_67__ ts__ (T_76_67__ st__ t)
parse_75__ ts__ (T_74_75__ (T_72_74__ (T_81_72__ st__) t))
    = parse_67__ ts__ (T_81_67__ st__ t)
parse_75__ ts__ (T_74_75__ (T_72_74__ (T_86_72__ st__) t))
    = parse_67__ ts__ (T_86_67__ st__ t)

parse_76__ (LexLam : tr__) st__ = parse_51__ tr__ (T_76_51__ st__)
parse_76__ (LexParL : tr__) st__ = parse_72__ tr__ (T_76_72__ st__)
parse_76__ (LexVar v1 : tr__) st__ = parse_69__ tr__ (T_76_69__ st__ v1)
parse_76__ (LexCon v1 : tr__) st__ = parse_70__ tr__ (T_76_70__ st__ v1)
parse_76__ (LexInt v1 : tr__) st__ = parse_71__ tr__ (T_76_71__ st__ v1)
parse_76__ (LexCase : tr__) st__ = parse_55__ tr__ (T_76_55__ st__)
parse_76__ (LexLet : tr__) st__ = parse_61__ tr__ (T_76_61__ st__)
parse_76__ ts__ st__ = frown ts__

parse_77__ (LexParR : tr__) st__ = parse_78__ tr__ (T_77_78__ st__)
parse_77__ ts__ st__ = frown ts__

parse_78__ ts__
    (T_77_78__ (T_76_77__ (T_74_76__ (T_72_74__ (T_11_72__ st__) u)) v))
    = parse_67__ ts__ (T_11_67__ st__ (App (App (Con ",") u) v))
parse_78__ ts__
    (T_77_78__ (T_76_77__ (T_74_76__ (T_72_74__ (T_48_72__ st__) u)) v))
    = parse_68__ ts__ (T_48_68__ st__ (App (App (Con ",") u) v))
parse_78__ ts__
    (T_77_78__ (T_76_77__ (T_74_76__ (T_72_74__ (T_49_72__ st__) u)) v))
    = parse_67__ ts__ (T_49_67__ st__ (App (App (Con ",") u) v))
parse_78__ ts__
    (T_77_78__ (T_76_77__ (T_74_76__ (T_72_74__ (T_53_72__ st__) u)) v))
    = parse_67__ ts__ (T_53_67__ st__ (App (App (Con ",") u) v))
parse_78__ ts__
    (T_77_78__ (T_76_77__ (T_74_76__ (T_72_74__ (T_55_72__ st__) u)) v))
    = parse_67__ ts__ (T_55_67__ st__ (App (App (Con ",") u) v))
parse_78__ ts__
    (T_77_78__ (T_76_77__ (T_74_76__ (T_72_74__ (T_65_72__ st__) u)) v))
    = parse_67__ ts__ (T_65_67__ st__ (App (App (Con ",") u) v))
parse_78__ ts__
    (T_77_78__ (T_76_77__ (T_74_76__ (T_72_74__ (T_72_72__ st__) u)) v))
    = parse_67__ ts__ (T_72_67__ st__ (App (App (Con ",") u) v))
parse_78__ ts__
    (T_77_78__ (T_76_77__ (T_74_76__ (T_72_74__ (T_76_72__ st__) u)) v))
    = parse_67__ ts__ (T_76_67__ st__ (App (App (Con ",") u) v))
parse_78__ ts__
    (T_77_78__ (T_76_77__ (T_74_76__ (T_72_74__ (T_81_72__ st__) u)) v))
    = parse_67__ ts__ (T_81_67__ st__ (App (App (Con ",") u) v))
parse_78__ ts__
    (T_77_78__ (T_76_77__ (T_74_76__ (T_72_74__ (T_86_72__ st__) u)) v))
    = parse_67__ ts__ (T_86_67__ st__ (App (App (Con ",") u) v))

parse_79__ ts__@(LexDef : tr__) st__ = parse_80__ ts__ (T_79_80__ st__ ([]))
parse_79__ (LexVar v1 : tr__) st__ = parse_20__ tr__ (T_79_20__ st__ v1)
parse_79__ ts__ st__ = frown ts__

parse_80__ (LexDef : tr__) st__ = parse_81__ tr__ (T_80_81__ st__)
parse_80__ ts__ st__ = frown ts__

parse_81__ (LexLam : tr__) st__ = parse_51__ tr__ (T_81_51__ st__)
parse_81__ (LexParL : tr__) st__ = parse_72__ tr__ (T_81_72__ st__)
parse_81__ (LexVar v1 : tr__) st__ = parse_69__ tr__ (T_81_69__ st__ v1)
parse_81__ (LexCon v1 : tr__) st__ = parse_70__ tr__ (T_81_70__ st__ v1)
parse_81__ (LexInt v1 : tr__) st__ = parse_71__ tr__ (T_81_71__ st__ v1)
parse_81__ (LexCase : tr__) st__ = parse_55__ tr__ (T_81_55__ st__)
parse_81__ (LexLet : tr__) st__ = parse_61__ tr__ (T_81_61__ st__)
parse_81__ ts__ st__ = frown ts__

parse_82__ (LexSemi : tr__) st__ = parse_83__ tr__ (T_82_83__ st__)
parse_82__ ts__@(LexBraR : tr__)
    (T_81_82__ (T_80_81__ (T_79_80__ (T_62_79__ st__ v) ax)) t)
    = parse_63__ ts__ (T_62_63__ st__ ([(v, foldr Lam t ax)]))
parse_82__ ts__@(LexBraR : tr__)
    (T_81_82__ (T_80_81__ (T_79_80__ (T_83_79__ st__ v) ax)) t)
    = parse_84__ ts__ (T_83_84__ st__ ([(v, foldr Lam t ax)]))
parse_82__ ts__ st__ = frown ts__

parse_83__ (LexVar v1 : tr__) st__ = parse_79__ tr__ (T_83_79__ st__ v1)
parse_83__ ts__ st__ = frown ts__

parse_84__ ts__
    (T_83_84__
             (T_82_83__
                  (T_81_82__ (T_80_81__ (T_79_80__ (T_62_79__ st__ v) ax)) t))
         dx) = parse_63__ ts__ (T_62_63__ st__ ((v, foldr Lam t ax):dx))
parse_84__ ts__
    (T_83_84__
             (T_82_83__
                  (T_81_82__ (T_80_81__ (T_79_80__ (T_83_79__ st__ v) ax)) t))
         dx) = parse_84__ ts__ (T_83_84__ st__ ((v, foldr Lam t ax):dx))

parse_85__ (LexArr : tr__) st__ = parse_86__ tr__ (T_85_86__ st__)
parse_85__ ts__ st__ = frown ts__

parse_86__ (LexLam : tr__) st__ = parse_51__ tr__ (T_86_51__ st__)
parse_86__ (LexParL : tr__) st__ = parse_72__ tr__ (T_86_72__ st__)
parse_86__ (LexVar v1 : tr__) st__ = parse_69__ tr__ (T_86_69__ st__ v1)
parse_86__ (LexCon v1 : tr__) st__ = parse_70__ tr__ (T_86_70__ st__ v1)
parse_86__ (LexInt v1 : tr__) st__ = parse_71__ tr__ (T_86_71__ st__ v1)
parse_86__ (LexCase : tr__) st__ = parse_55__ tr__ (T_86_55__ st__)
parse_86__ (LexLet : tr__) st__ = parse_61__ tr__ (T_86_61__ st__)
parse_86__ ts__ st__ = frown ts__

parse_87__ (LexSemi : tr__) st__ = parse_88__ tr__ (T_87_88__ st__)
parse_87__ ts__@(LexBraR : tr__) (T_86_87__ (T_85_86__ (T_58_85__ st__ p)) t)
    = parse_59__ ts__ (T_58_59__ st__ ([(p, t)]))
parse_87__ ts__@(LexBraR : tr__) (T_86_87__ (T_85_86__ (T_88_85__ st__ p)) t)
    = parse_89__ ts__ (T_88_89__ st__ ([(p, t)]))
parse_87__ ts__ st__ = frown ts__

parse_88__ (LexParL : tr__) st__ = parse_92__ tr__ (T_88_92__ st__)
parse_88__ (LexCon v1 : tr__) st__ = parse_90__ tr__ (T_88_90__ st__ v1)
parse_88__ (LexInt v1 : tr__) st__ = parse_97__ tr__ (T_88_97__ st__ v1)
parse_88__ ts__ st__ = frown ts__

parse_89__ ts__
    (T_88_89__ (T_87_88__ (T_86_87__ (T_85_86__ (T_58_85__ st__ p)) t)) cx)
    = parse_59__ ts__ (T_58_59__ st__ ((p, t):cx))
parse_89__ ts__
    (T_88_89__ (T_87_88__ (T_86_87__ (T_85_86__ (T_88_85__ st__ p)) t)) cx)
    = parse_89__ ts__ (T_88_89__ st__ ((p, t):cx))

parse_90__ ts__@(LexArr : tr__) st__ = parse_91__ ts__ (T_90_91__ st__ ([]))
parse_90__ (LexVar v1 : tr__) st__ = parse_20__ tr__ (T_90_20__ st__ v1)
parse_90__ ts__ st__ = frown ts__

parse_91__ ts__ (T_90_91__ (T_58_90__ st__ c) px)
    = parse_85__ ts__ (T_58_85__ st__ (PatCon c px))
parse_91__ ts__ (T_90_91__ (T_88_90__ st__ c) px)
    = parse_85__ ts__ (T_88_85__ st__ (PatCon c px))

parse_92__ (LexVar v1 : tr__) st__ = parse_93__ tr__ (T_92_93__ st__ v1)
parse_92__ ts__ st__ = frown ts__

parse_93__ (LexComa : tr__) st__ = parse_94__ tr__ (T_93_94__ st__)
parse_93__ ts__ st__ = frown ts__

parse_94__ (LexVar v1 : tr__) st__ = parse_95__ tr__ (T_94_95__ st__ v1)
parse_94__ ts__ st__ = frown ts__

parse_95__ (LexParR : tr__) st__ = parse_96__ tr__ (T_95_96__ st__)
parse_95__ ts__ st__ = frown ts__

parse_96__ ts__
    (T_95_96__ (T_94_95__ (T_93_94__ (T_92_93__ (T_58_92__ st__) u)) v))
    = parse_85__ ts__ (T_58_85__ st__ (PatCon "," [u, v]))
parse_96__ ts__
    (T_95_96__ (T_94_95__ (T_93_94__ (T_92_93__ (T_88_92__ st__) u)) v))
    = parse_85__ ts__ (T_88_85__ st__ (PatCon "," [u, v]))

parse_97__ ts__ (T_58_97__ st__ i) = parse_85__ ts__ (T_58_85__ st__ (PatInt i))
parse_97__ ts__ (T_88_97__ st__ i) = parse_85__ ts__ (T_88_85__ st__ (PatInt i))


{- )-: frown -}



frown remain = fail (show (take 10 remain))

--------- Parse programs in files

parseFile :: String -> IO [Program]
parseFile file =
    do program <- readFile file
       top (segment program)

--------- Lexical analysis: top-level function

skiplf :: String -> String
skiplf = dropWhile ('\n' /=)

copydoc :: String -> ([String], String)
copydoc ('\n':cs@('-':'-':_)) = (doc:docs, rest)
    where (doc, wt) = span ('\n' /=) cs
          (docs, rest) = copydoc wt
copydoc cs = ([], cs)

segment :: String -> [Terminal]
segment [] = [LexNext]
segment ('\n':cs@('\n':'-':'-':_)) =
    let (doc, wt) = copydoc cs
    in LexNext : (map LexDoc doc ++ segment wt)
segment ('-':'-':cs) = segment (skiplf cs)
segment ('\n':'>':cs) = LexNext : segment (skiplf cs)
segment ('\n':'\n':'>':cs) = LexNext : segment (skiplf cs)
segment ('\n':cs@('\n':_)) = LexNext : segment cs
segment (c:cs) | isSpace c = segment cs
segment input =
    let (word, wt) = span isIdentChar input
        (symbol, st) = span isSymChar input
    in if null word
       then lexSymbol symbol ++ segment st
       else lexIdent word : segment wt

--------- Lexical analysis: symbols and operators

isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_'

isSymChar :: Char -> Bool
isSymChar c = not (isIdentChar c || isSpace c)

keysyms0 :: [(Char, Terminal)]
keysyms0 = [(';',  LexSemi), (',',  LexComa),
            ('\\', LexLam),
            ('(',  LexParL), (')',  LexParR),
            ('{',  LexBraL), ('}',  LexBraR)]

-- Note that here I use the same token, LexOp, to represent three
-- different integer binary operators.  This is hack, but as long as we
-- only type (but not evaluate) the programs, there really is no need to
-- distinguish the operators, which all have the same type.

keysyms :: [(String, Terminal)]
keysyms = [("+",  LexOp),  ("=",  LexDef),
           ("*",  LexOp),  ("/",  LexOp),
           ("->", LexArr), ("::", LexType)]

lexSymbol :: String -> [Terminal]
lexSymbol [] = []
lexSymbol symbol@(s:sx) =
    case lookup s keysyms0 of
      Just token -> token:lexSymbol sx
      Nothing -> case lookup symbol keysyms of
                   Just token -> [token]
                   Nothing -> [LexError]

--------- Lexical analysis: keywords and identifiers

keywords :: [(String, Terminal)]
keywords = [("data", LexData), ("where", LexWhere),
            ("case", LexCase), ("of",    LexOf),
            ("let",  LexLet),  ("in",    LexIn)]

lexIdent :: String -> Terminal
lexIdent word =
    if all isDigit word then LexInt (read word)
    else if isUpper (head word) then LexCon word
         else if isLower (head word) then
                  case lookup word keywords of
                    Just token -> token
                    Nothing -> LexVar word
              else LexError

