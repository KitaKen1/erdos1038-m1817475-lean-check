import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block154

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block154

open Set

def block154W1 : Rat := ((4291467441125973 : Rat) / 2000000000000000)
def block154W2 : Rat := (0 : Rat)
def block154W3 : Rat := ((17168721654531977 : Rat) / 100000000000000000)
def block154W4 : Rat := ((8171873467124889 : Rat) / 100000000000000000)
def block154S1 : Rat := ((18174751 : Rat) / 10000000)
def block154S2 : Rat := ((511587 : Rat) / 200000)
def block154S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block154S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block154V (y : ℝ) : ℝ :=
  ratPotential block154W1 block154W2 block154W3 block154W4 block154S1 block154S2 block154S3 block154S4 y

def block154LeftParamsCertificate : Bool :=
  allBoxesSameParams block154LeftBoxes block154W1 block154W2 block154W3 block154W4 block154S1 block154S2 block154S3 block154S4

theorem block154LeftParamsCertificate_eq_true :
    block154LeftParamsCertificate = true := by
  native_decide

theorem block154_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block154LeftL : ℝ) (block154LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block154S1 : ℝ))
    (hy2ne : y ≠ (block154S2 : ℝ))
    (hy3ne : y ≠ (block154S3 : ℝ))
    (hy4ne : y ≠ (block154S4 : ℝ)) :
    0 < block154V y := by
  have hcert := block154LeftCertificate_eq_true
  unfold block154LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block154LeftBoxes) (lo := block154LeftL) (hi := block154LeftR)
    (w1 := block154W1) (w2 := block154W2) (w3 := block154W3) (w4 := block154W4)
    (s1 := block154S1) (s2 := block154S2) (s3 := block154S3) (s4 := block154S4)
    hboxes hcover block154LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block154RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block154RightChunk000 block154W1 block154W2 block154W3 block154W4 block154S1 block154S2 block154S3 block154S4

theorem block154RightChunk000ParamsCertificate_eq_true :
    block154RightChunk000ParamsCertificate = true := by
  native_decide

theorem block154_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block154RightChunk000L : ℝ) (block154RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block154S1 : ℝ))
    (hy2ne : y ≠ (block154S2 : ℝ))
    (hy3ne : y ≠ (block154S3 : ℝ))
    (hy4ne : y ≠ (block154S4 : ℝ)) :
    0 < block154V y := by
  have hcert := block154RightChunk000Certificate_eq_true
  unfold block154RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block154RightChunk000) (lo := block154RightChunk000L) (hi := block154RightChunk000R)
    (w1 := block154W1) (w2 := block154W2) (w3 := block154W3) (w4 := block154W4)
    (s1 := block154S1) (s2 := block154S2) (s3 := block154S3) (s4 := block154S4)
    hboxes hcover block154RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block154_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block154RightL : ℝ) (block154RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block154S1 : ℝ))
    (hy2ne : y ≠ (block154S2 : ℝ))
    (hy3ne : y ≠ (block154S3 : ℝ))
    (hy4ne : y ≠ (block154S4 : ℝ)) :
    0 < block154V y := by
  have hL : (block154RightChunk000L : ℝ) = (block154RightL : ℝ) := by
    norm_num [block154RightChunk000L, block154RightL]
  have hR : (block154RightChunk000R : ℝ) = (block154RightR : ℝ) := by
    norm_num [block154RightChunk000R, block154RightR]
  have hyc : y ∈ Icc (block154RightChunk000L : ℝ) (block154RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block154_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block154_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block154LeftL : ℝ) (block154LeftR : ℝ) →
    y ≠ 0 → y ≠ (block154S1 : ℝ) → y ≠ (block154S2 : ℝ) →
    y ≠ (block154S3 : ℝ) → y ≠ (block154S4 : ℝ) → 0 < block154V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block154RightL : ℝ) (block154RightR : ℝ) →
    y ≠ 0 → y ≠ (block154S1 : ℝ) → y ≠ (block154S2 : ℝ) →
    y ≠ (block154S3 : ℝ) → y ≠ (block154S4 : ℝ) → 0 < block154V y)

theorem block154_reallog_certificate_proof :
    block154_reallog_certificate := by
  exact ⟨block154_left_V_pos, block154_right_V_pos⟩

end Block154
end M1817475
end Erdos1038Lean
