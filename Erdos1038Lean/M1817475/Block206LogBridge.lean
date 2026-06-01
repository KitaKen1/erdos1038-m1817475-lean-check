import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block206

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block206

open Set

def block206W1 : Rat := ((9691445827599363 : Rat) / 10000000000000000)
def block206W2 : Rat := ((5215832551043879 : Rat) / 100000000000000000)
def block206W3 : Rat := ((17639902091340579 : Rat) / 100000000000000000)
def block206W4 : Rat := ((4840188261244877 : Rat) / 50000000000000000)
def block206S1 : Rat := ((18174751 : Rat) / 10000000)
def block206S2 : Rat := ((511587 : Rat) / 200000)
def block206S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block206S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block206V (y : ℝ) : ℝ :=
  ratPotential block206W1 block206W2 block206W3 block206W4 block206S1 block206S2 block206S3 block206S4 y

def block206LeftParamsCertificate : Bool :=
  allBoxesSameParams block206LeftBoxes block206W1 block206W2 block206W3 block206W4 block206S1 block206S2 block206S3 block206S4

theorem block206LeftParamsCertificate_eq_true :
    block206LeftParamsCertificate = true := by
  native_decide

theorem block206_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block206LeftL : ℝ) (block206LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block206S1 : ℝ))
    (hy2ne : y ≠ (block206S2 : ℝ))
    (hy3ne : y ≠ (block206S3 : ℝ))
    (hy4ne : y ≠ (block206S4 : ℝ)) :
    0 < block206V y := by
  have hcert := block206LeftCertificate_eq_true
  unfold block206LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block206LeftBoxes) (lo := block206LeftL) (hi := block206LeftR)
    (w1 := block206W1) (w2 := block206W2) (w3 := block206W3) (w4 := block206W4)
    (s1 := block206S1) (s2 := block206S2) (s3 := block206S3) (s4 := block206S4)
    hboxes hcover block206LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block206RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block206RightChunk000 block206W1 block206W2 block206W3 block206W4 block206S1 block206S2 block206S3 block206S4

theorem block206RightChunk000ParamsCertificate_eq_true :
    block206RightChunk000ParamsCertificate = true := by
  native_decide

theorem block206_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block206RightChunk000L : ℝ) (block206RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block206S1 : ℝ))
    (hy2ne : y ≠ (block206S2 : ℝ))
    (hy3ne : y ≠ (block206S3 : ℝ))
    (hy4ne : y ≠ (block206S4 : ℝ)) :
    0 < block206V y := by
  have hcert := block206RightChunk000Certificate_eq_true
  unfold block206RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block206RightChunk000) (lo := block206RightChunk000L) (hi := block206RightChunk000R)
    (w1 := block206W1) (w2 := block206W2) (w3 := block206W3) (w4 := block206W4)
    (s1 := block206S1) (s2 := block206S2) (s3 := block206S3) (s4 := block206S4)
    hboxes hcover block206RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block206RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block206RightChunk001 block206W1 block206W2 block206W3 block206W4 block206S1 block206S2 block206S3 block206S4

theorem block206RightChunk001ParamsCertificate_eq_true :
    block206RightChunk001ParamsCertificate = true := by
  native_decide

theorem block206_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block206RightChunk001L : ℝ) (block206RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block206S1 : ℝ))
    (hy2ne : y ≠ (block206S2 : ℝ))
    (hy3ne : y ≠ (block206S3 : ℝ))
    (hy4ne : y ≠ (block206S4 : ℝ)) :
    0 < block206V y := by
  have hcert := block206RightChunk001Certificate_eq_true
  unfold block206RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block206RightChunk001) (lo := block206RightChunk001L) (hi := block206RightChunk001R)
    (w1 := block206W1) (w2 := block206W2) (w3 := block206W3) (w4 := block206W4)
    (s1 := block206S1) (s2 := block206S2) (s3 := block206S3) (s4 := block206S4)
    hboxes hcover block206RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block206RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block206RightChunk002 block206W1 block206W2 block206W3 block206W4 block206S1 block206S2 block206S3 block206S4

theorem block206RightChunk002ParamsCertificate_eq_true :
    block206RightChunk002ParamsCertificate = true := by
  native_decide

theorem block206_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block206RightChunk002L : ℝ) (block206RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block206S1 : ℝ))
    (hy2ne : y ≠ (block206S2 : ℝ))
    (hy3ne : y ≠ (block206S3 : ℝ))
    (hy4ne : y ≠ (block206S4 : ℝ)) :
    0 < block206V y := by
  have hcert := block206RightChunk002Certificate_eq_true
  unfold block206RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block206RightChunk002) (lo := block206RightChunk002L) (hi := block206RightChunk002R)
    (w1 := block206W1) (w2 := block206W2) (w3 := block206W3) (w4 := block206W4)
    (s1 := block206S1) (s2 := block206S2) (s3 := block206S3) (s4 := block206S4)
    hboxes hcover block206RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block206RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block206RightChunk003 block206W1 block206W2 block206W3 block206W4 block206S1 block206S2 block206S3 block206S4

theorem block206RightChunk003ParamsCertificate_eq_true :
    block206RightChunk003ParamsCertificate = true := by
  native_decide

theorem block206_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block206RightChunk003L : ℝ) (block206RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block206S1 : ℝ))
    (hy2ne : y ≠ (block206S2 : ℝ))
    (hy3ne : y ≠ (block206S3 : ℝ))
    (hy4ne : y ≠ (block206S4 : ℝ)) :
    0 < block206V y := by
  have hcert := block206RightChunk003Certificate_eq_true
  unfold block206RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block206RightChunk003) (lo := block206RightChunk003L) (hi := block206RightChunk003R)
    (w1 := block206W1) (w2 := block206W2) (w3 := block206W3) (w4 := block206W4)
    (s1 := block206S1) (s2 := block206S2) (s3 := block206S3) (s4 := block206S4)
    hboxes hcover block206RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block206RightChunk004ParamsCertificate : Bool :=
  allBoxesSameParams block206RightChunk004 block206W1 block206W2 block206W3 block206W4 block206S1 block206S2 block206S3 block206S4

theorem block206RightChunk004ParamsCertificate_eq_true :
    block206RightChunk004ParamsCertificate = true := by
  native_decide

theorem block206_right_chunk004_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block206RightChunk004L : ℝ) (block206RightChunk004R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block206S1 : ℝ))
    (hy2ne : y ≠ (block206S2 : ℝ))
    (hy3ne : y ≠ (block206S3 : ℝ))
    (hy4ne : y ≠ (block206S4 : ℝ)) :
    0 < block206V y := by
  have hcert := block206RightChunk004Certificate_eq_true
  unfold block206RightChunk004Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block206RightChunk004) (lo := block206RightChunk004L) (hi := block206RightChunk004R)
    (w1 := block206W1) (w2 := block206W2) (w3 := block206W3) (w4 := block206W4)
    (s1 := block206S1) (s2 := block206S2) (s3 := block206S3) (s4 := block206S4)
    hboxes hcover block206RightChunk004ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block206_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block206RightL : ℝ) (block206RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block206S1 : ℝ))
    (hy2ne : y ≠ (block206S2 : ℝ))
    (hy3ne : y ≠ (block206S3 : ℝ))
    (hy4ne : y ≠ (block206S4 : ℝ)) :
    0 < block206V y := by
  by_cases h0 : y ≤ (block206RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block206RightChunk000L : ℝ) (block206RightChunk000R : ℝ) := by
      have hL : (block206RightChunk000L : ℝ) = (block206RightL : ℝ) := by
        norm_num [block206RightChunk000L, block206RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block206_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block206RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block206RightChunk001L : ℝ) (block206RightChunk001R : ℝ) := by
        have hprev : (block206RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block206RightChunk001L : ℝ) = (block206RightChunk000R : ℝ) := by
          norm_num [block206RightChunk001L, block206RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block206_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block206RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block206RightChunk002L : ℝ) (block206RightChunk002R : ℝ) := by
          have hprev : (block206RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block206RightChunk002L : ℝ) = (block206RightChunk001R : ℝ) := by
            norm_num [block206RightChunk002L, block206RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block206_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        by_cases h3 : y ≤ (block206RightChunk003R : ℝ)
        · have hyc : y ∈ Icc (block206RightChunk003L : ℝ) (block206RightChunk003R : ℝ) := by
            have hprev : (block206RightChunk002R : ℝ) < y := lt_of_not_ge h2
            have hL : (block206RightChunk003L : ℝ) = (block206RightChunk002R : ℝ) := by
              norm_num [block206RightChunk003L, block206RightChunk002R]
            constructor
            · linarith [hprev, hL]
            · exact h3
          exact block206_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
        ·
          have hprev : (block206RightChunk003R : ℝ) < y := lt_of_not_ge h3
          have hL : (block206RightChunk004L : ℝ) = (block206RightChunk003R : ℝ) := by
            norm_num [block206RightChunk004L, block206RightChunk003R]
          have hR : (block206RightChunk004R : ℝ) = (block206RightR : ℝ) := by
            norm_num [block206RightChunk004R, block206RightR]
          have hyc : y ∈ Icc (block206RightChunk004L : ℝ) (block206RightChunk004R : ℝ) := by
            constructor
            · linarith [hprev, hL]
            · linarith [hy.2, hR]
          exact block206_right_chunk004_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block206_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block206LeftL : ℝ) (block206LeftR : ℝ) →
    y ≠ 0 → y ≠ (block206S1 : ℝ) → y ≠ (block206S2 : ℝ) →
    y ≠ (block206S3 : ℝ) → y ≠ (block206S4 : ℝ) → 0 < block206V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block206RightL : ℝ) (block206RightR : ℝ) →
    y ≠ 0 → y ≠ (block206S1 : ℝ) → y ≠ (block206S2 : ℝ) →
    y ≠ (block206S3 : ℝ) → y ≠ (block206S4 : ℝ) → 0 < block206V y)

theorem block206_reallog_certificate_proof :
    block206_reallog_certificate := by
  exact ⟨block206_left_V_pos, block206_right_V_pos⟩

end Block206
end M1817475
end Erdos1038Lean
