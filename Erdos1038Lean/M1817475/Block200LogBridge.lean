import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block200

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block200

open Set

def block200W1 : Rat := ((9728506304123521 : Rat) / 10000000000000000)
def block200W2 : Rat := ((25502664711046747 : Rat) / 500000000000000000)
def block200W3 : Rat := ((142321890954761 : Rat) / 800000000000000)
def block200W4 : Rat := ((2401767450861289 : Rat) / 25000000000000000)
def block200S1 : Rat := ((18174751 : Rat) / 10000000)
def block200S2 : Rat := ((511587 : Rat) / 200000)
def block200S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block200S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block200V (y : ℝ) : ℝ :=
  ratPotential block200W1 block200W2 block200W3 block200W4 block200S1 block200S2 block200S3 block200S4 y

def block200LeftParamsCertificate : Bool :=
  allBoxesSameParams block200LeftBoxes block200W1 block200W2 block200W3 block200W4 block200S1 block200S2 block200S3 block200S4

theorem block200LeftParamsCertificate_eq_true :
    block200LeftParamsCertificate = true := by
  native_decide

theorem block200_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block200LeftL : ℝ) (block200LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block200S1 : ℝ))
    (hy2ne : y ≠ (block200S2 : ℝ))
    (hy3ne : y ≠ (block200S3 : ℝ))
    (hy4ne : y ≠ (block200S4 : ℝ)) :
    0 < block200V y := by
  have hcert := block200LeftCertificate_eq_true
  unfold block200LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block200LeftBoxes) (lo := block200LeftL) (hi := block200LeftR)
    (w1 := block200W1) (w2 := block200W2) (w3 := block200W3) (w4 := block200W4)
    (s1 := block200S1) (s2 := block200S2) (s3 := block200S3) (s4 := block200S4)
    hboxes hcover block200LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block200RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block200RightChunk000 block200W1 block200W2 block200W3 block200W4 block200S1 block200S2 block200S3 block200S4

theorem block200RightChunk000ParamsCertificate_eq_true :
    block200RightChunk000ParamsCertificate = true := by
  native_decide

theorem block200_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block200RightChunk000L : ℝ) (block200RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block200S1 : ℝ))
    (hy2ne : y ≠ (block200S2 : ℝ))
    (hy3ne : y ≠ (block200S3 : ℝ))
    (hy4ne : y ≠ (block200S4 : ℝ)) :
    0 < block200V y := by
  have hcert := block200RightChunk000Certificate_eq_true
  unfold block200RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block200RightChunk000) (lo := block200RightChunk000L) (hi := block200RightChunk000R)
    (w1 := block200W1) (w2 := block200W2) (w3 := block200W3) (w4 := block200W4)
    (s1 := block200S1) (s2 := block200S2) (s3 := block200S3) (s4 := block200S4)
    hboxes hcover block200RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block200RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block200RightChunk001 block200W1 block200W2 block200W3 block200W4 block200S1 block200S2 block200S3 block200S4

theorem block200RightChunk001ParamsCertificate_eq_true :
    block200RightChunk001ParamsCertificate = true := by
  native_decide

theorem block200_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block200RightChunk001L : ℝ) (block200RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block200S1 : ℝ))
    (hy2ne : y ≠ (block200S2 : ℝ))
    (hy3ne : y ≠ (block200S3 : ℝ))
    (hy4ne : y ≠ (block200S4 : ℝ)) :
    0 < block200V y := by
  have hcert := block200RightChunk001Certificate_eq_true
  unfold block200RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block200RightChunk001) (lo := block200RightChunk001L) (hi := block200RightChunk001R)
    (w1 := block200W1) (w2 := block200W2) (w3 := block200W3) (w4 := block200W4)
    (s1 := block200S1) (s2 := block200S2) (s3 := block200S3) (s4 := block200S4)
    hboxes hcover block200RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block200RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block200RightChunk002 block200W1 block200W2 block200W3 block200W4 block200S1 block200S2 block200S3 block200S4

theorem block200RightChunk002ParamsCertificate_eq_true :
    block200RightChunk002ParamsCertificate = true := by
  native_decide

theorem block200_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block200RightChunk002L : ℝ) (block200RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block200S1 : ℝ))
    (hy2ne : y ≠ (block200S2 : ℝ))
    (hy3ne : y ≠ (block200S3 : ℝ))
    (hy4ne : y ≠ (block200S4 : ℝ)) :
    0 < block200V y := by
  have hcert := block200RightChunk002Certificate_eq_true
  unfold block200RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block200RightChunk002) (lo := block200RightChunk002L) (hi := block200RightChunk002R)
    (w1 := block200W1) (w2 := block200W2) (w3 := block200W3) (w4 := block200W4)
    (s1 := block200S1) (s2 := block200S2) (s3 := block200S3) (s4 := block200S4)
    hboxes hcover block200RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block200RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block200RightChunk003 block200W1 block200W2 block200W3 block200W4 block200S1 block200S2 block200S3 block200S4

theorem block200RightChunk003ParamsCertificate_eq_true :
    block200RightChunk003ParamsCertificate = true := by
  native_decide

theorem block200_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block200RightChunk003L : ℝ) (block200RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block200S1 : ℝ))
    (hy2ne : y ≠ (block200S2 : ℝ))
    (hy3ne : y ≠ (block200S3 : ℝ))
    (hy4ne : y ≠ (block200S4 : ℝ)) :
    0 < block200V y := by
  have hcert := block200RightChunk003Certificate_eq_true
  unfold block200RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block200RightChunk003) (lo := block200RightChunk003L) (hi := block200RightChunk003R)
    (w1 := block200W1) (w2 := block200W2) (w3 := block200W3) (w4 := block200W4)
    (s1 := block200S1) (s2 := block200S2) (s3 := block200S3) (s4 := block200S4)
    hboxes hcover block200RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block200RightChunk004ParamsCertificate : Bool :=
  allBoxesSameParams block200RightChunk004 block200W1 block200W2 block200W3 block200W4 block200S1 block200S2 block200S3 block200S4

theorem block200RightChunk004ParamsCertificate_eq_true :
    block200RightChunk004ParamsCertificate = true := by
  native_decide

theorem block200_right_chunk004_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block200RightChunk004L : ℝ) (block200RightChunk004R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block200S1 : ℝ))
    (hy2ne : y ≠ (block200S2 : ℝ))
    (hy3ne : y ≠ (block200S3 : ℝ))
    (hy4ne : y ≠ (block200S4 : ℝ)) :
    0 < block200V y := by
  have hcert := block200RightChunk004Certificate_eq_true
  unfold block200RightChunk004Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block200RightChunk004) (lo := block200RightChunk004L) (hi := block200RightChunk004R)
    (w1 := block200W1) (w2 := block200W2) (w3 := block200W3) (w4 := block200W4)
    (s1 := block200S1) (s2 := block200S2) (s3 := block200S3) (s4 := block200S4)
    hboxes hcover block200RightChunk004ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block200RightChunk005ParamsCertificate : Bool :=
  allBoxesSameParams block200RightChunk005 block200W1 block200W2 block200W3 block200W4 block200S1 block200S2 block200S3 block200S4

theorem block200RightChunk005ParamsCertificate_eq_true :
    block200RightChunk005ParamsCertificate = true := by
  native_decide

theorem block200_right_chunk005_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block200RightChunk005L : ℝ) (block200RightChunk005R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block200S1 : ℝ))
    (hy2ne : y ≠ (block200S2 : ℝ))
    (hy3ne : y ≠ (block200S3 : ℝ))
    (hy4ne : y ≠ (block200S4 : ℝ)) :
    0 < block200V y := by
  have hcert := block200RightChunk005Certificate_eq_true
  unfold block200RightChunk005Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block200RightChunk005) (lo := block200RightChunk005L) (hi := block200RightChunk005R)
    (w1 := block200W1) (w2 := block200W2) (w3 := block200W3) (w4 := block200W4)
    (s1 := block200S1) (s2 := block200S2) (s3 := block200S3) (s4 := block200S4)
    hboxes hcover block200RightChunk005ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block200RightChunk006ParamsCertificate : Bool :=
  allBoxesSameParams block200RightChunk006 block200W1 block200W2 block200W3 block200W4 block200S1 block200S2 block200S3 block200S4

theorem block200RightChunk006ParamsCertificate_eq_true :
    block200RightChunk006ParamsCertificate = true := by
  native_decide

theorem block200_right_chunk006_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block200RightChunk006L : ℝ) (block200RightChunk006R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block200S1 : ℝ))
    (hy2ne : y ≠ (block200S2 : ℝ))
    (hy3ne : y ≠ (block200S3 : ℝ))
    (hy4ne : y ≠ (block200S4 : ℝ)) :
    0 < block200V y := by
  have hcert := block200RightChunk006Certificate_eq_true
  unfold block200RightChunk006Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block200RightChunk006) (lo := block200RightChunk006L) (hi := block200RightChunk006R)
    (w1 := block200W1) (w2 := block200W2) (w3 := block200W3) (w4 := block200W4)
    (s1 := block200S1) (s2 := block200S2) (s3 := block200S3) (s4 := block200S4)
    hboxes hcover block200RightChunk006ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block200_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block200RightL : ℝ) (block200RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block200S1 : ℝ))
    (hy2ne : y ≠ (block200S2 : ℝ))
    (hy3ne : y ≠ (block200S3 : ℝ))
    (hy4ne : y ≠ (block200S4 : ℝ)) :
    0 < block200V y := by
  by_cases h0 : y ≤ (block200RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block200RightChunk000L : ℝ) (block200RightChunk000R : ℝ) := by
      have hL : (block200RightChunk000L : ℝ) = (block200RightL : ℝ) := by
        norm_num [block200RightChunk000L, block200RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block200_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block200RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block200RightChunk001L : ℝ) (block200RightChunk001R : ℝ) := by
        have hprev : (block200RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block200RightChunk001L : ℝ) = (block200RightChunk000R : ℝ) := by
          norm_num [block200RightChunk001L, block200RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block200_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block200RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block200RightChunk002L : ℝ) (block200RightChunk002R : ℝ) := by
          have hprev : (block200RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block200RightChunk002L : ℝ) = (block200RightChunk001R : ℝ) := by
            norm_num [block200RightChunk002L, block200RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block200_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        by_cases h3 : y ≤ (block200RightChunk003R : ℝ)
        · have hyc : y ∈ Icc (block200RightChunk003L : ℝ) (block200RightChunk003R : ℝ) := by
            have hprev : (block200RightChunk002R : ℝ) < y := lt_of_not_ge h2
            have hL : (block200RightChunk003L : ℝ) = (block200RightChunk002R : ℝ) := by
              norm_num [block200RightChunk003L, block200RightChunk002R]
            constructor
            · linarith [hprev, hL]
            · exact h3
          exact block200_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
        ·
          by_cases h4 : y ≤ (block200RightChunk004R : ℝ)
          · have hyc : y ∈ Icc (block200RightChunk004L : ℝ) (block200RightChunk004R : ℝ) := by
              have hprev : (block200RightChunk003R : ℝ) < y := lt_of_not_ge h3
              have hL : (block200RightChunk004L : ℝ) = (block200RightChunk003R : ℝ) := by
                norm_num [block200RightChunk004L, block200RightChunk003R]
              constructor
              · linarith [hprev, hL]
              · exact h4
            exact block200_right_chunk004_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
          ·
            by_cases h5 : y ≤ (block200RightChunk005R : ℝ)
            · have hyc : y ∈ Icc (block200RightChunk005L : ℝ) (block200RightChunk005R : ℝ) := by
                have hprev : (block200RightChunk004R : ℝ) < y := lt_of_not_ge h4
                have hL : (block200RightChunk005L : ℝ) = (block200RightChunk004R : ℝ) := by
                  norm_num [block200RightChunk005L, block200RightChunk004R]
                constructor
                · linarith [hprev, hL]
                · exact h5
              exact block200_right_chunk005_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
            ·
              have hprev : (block200RightChunk005R : ℝ) < y := lt_of_not_ge h5
              have hL : (block200RightChunk006L : ℝ) = (block200RightChunk005R : ℝ) := by
                norm_num [block200RightChunk006L, block200RightChunk005R]
              have hR : (block200RightChunk006R : ℝ) = (block200RightR : ℝ) := by
                norm_num [block200RightChunk006R, block200RightR]
              have hyc : y ∈ Icc (block200RightChunk006L : ℝ) (block200RightChunk006R : ℝ) := by
                constructor
                · linarith [hprev, hL]
                · linarith [hy.2, hR]
              exact block200_right_chunk006_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block200_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block200LeftL : ℝ) (block200LeftR : ℝ) →
    y ≠ 0 → y ≠ (block200S1 : ℝ) → y ≠ (block200S2 : ℝ) →
    y ≠ (block200S3 : ℝ) → y ≠ (block200S4 : ℝ) → 0 < block200V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block200RightL : ℝ) (block200RightR : ℝ) →
    y ≠ 0 → y ≠ (block200S1 : ℝ) → y ≠ (block200S2 : ℝ) →
    y ≠ (block200S3 : ℝ) → y ≠ (block200S4 : ℝ) → 0 < block200V y)

theorem block200_reallog_certificate_proof :
    block200_reallog_certificate := by
  exact ⟨block200_left_V_pos, block200_right_V_pos⟩

end Block200
end M1817475
end Erdos1038Lean
