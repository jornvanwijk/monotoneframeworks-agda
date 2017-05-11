

module Everything where

{- definitions of notions of finiteness -}
open import Listable
open import Noetherian

open import Streamless
open import Bounded
open import AlmostFull


{- examples of noetherian sets -}
open import NoethExamples -- BoolNoeth


{- properties of notions of Noetherianness -}
open import NoethAccDecEq -- NoethDecEq
open import NoethRels -- NoethAcc→NoethAccS, NoethAccS→NoethSet, 
    -- NoethSet→NoethAccS, NoethAccS→NoethGame, NoethExposeX→Listable
open import StreamlessProps -- NoethAccS→StreamlessS, NoethAcc→Streamless
open import AlmostFullProps -- AFEq→NoethAcc, NoethAcc→AFEq


{- separating sets -}
open import NotNotIn -- separating NoethAcc from NoethAccS
open import MaybeProp -- separating NoethExpose from Bounded
open import PropSet -- separating Listability from NoethExpose

