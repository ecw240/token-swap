//! Time-weighted constant product calculator
use {
    crate::{
        curve::calculator::{
            map_zero_to_none, CurveCalculator, DynPack, RoundDirection, SwapWithoutFeesResult,
            TradeDirection, TradingTokenResult,
        },
        error::SwapError,
    },
    solana_program::{
        program_error::ProgramError,
        program_pack::{IsInitialized, Pack, Sealed},
    },
    spl_math::{precise_number::PreciseNumber},
    num_integer::Roots,
};

/// Time Weighted Constant Product Curve
#[derive(Clone, Debug, Default, PartialEq)]
pub struct TimeWeightedCurve;

/// Constant product swap calculation, factored out of the class for reuse
/// Implemented thinking:
///  swap = trade = amm
// 1. calculations
// 2. return the x_out (source_amount_swapped) and y_out (destination_amount_swapped)
// x token in -> produces y token out (so not technically a swap here)
pub fn swap(
    source_amount: u128, // x_in
    swap_source_amount: u128, // x 
    swap_destination_amount: u128, // y 
) -> Option<SwapWithoutFeesResult> {
    let invariant = swap_source_amount.checked_mul(swap_destination_amount)?;
    let total_source_amount = swap_source_amount.checked_add(source_amount)?;
    let source_in_shares = source_amount.checked_div(total_source_amount)?;
    let destination_amount_swapped = source_in_shares.checked_mul(swap_destination_amount)?;
    let destination_amount = invariant.checked_div(source_amount)?;
    let source_amount_swapped = map_zero_to_none(swap_source_amount.checked_sub(destination_amount)?)?;
    
    Some(SwapWithoutFeesResult {
        source_amount_swapped, 
        destination_amount_swapped, 
    })
}

// infinitesimal
// 1. if one sided -> swap (trade), this goes for arb opportunities too
// 2. calculations as let where appropriate* -> and call calculation functions in others* 
// 3. return the x_out and y_out
// Formulas in https://www.paradigm.xyz/2021/07/twamm/
#[warn(missing_docs)]
pub fn infinitesimal(
    destination_amount: u128, // y_in
    source_amount: u128, // x_in
    swap_source_amount: u128, // x
    swap_destination_amount: u128, // y
) -> Option<SwapWithoutFeesResult> 
    {
    // check in case if processing one way trade
    if map_zero_to_none(swap_source_amount) == None {
        swap(source_amount, swap_destination_amount, swap_source_amount);
    }
    else if map_zero_to_none(swap_destination_amount) == None {
        swap(source_amount, swap_source_amount, swap_destination_amount);
    }

    let k = swap_source_amount.checked_mul(swap_destination_amount)?;
    let x_amm_start_y_in = swap_source_amount.checked_mul(destination_amount)?.sqrt();
    let y_amm_start_x_in = swap_destination_amount.checked_mul(source_amount)?.sqrt();
    let c_num = x_amm_start_y_in.checked_sub(y_amm_start_x_in)?;
    let c_rhs = x_amm_start_y_in.checked_add(y_amm_start_x_in)?;
    let c = c_num.checked_div(c_rhs)?;

    let x_in_y_in_mul = source_amount.checked_mul(destination_amount)?;
    let exponent = 2 * (x_in_y_in_mul.checked_div(k)?.sqrt());

    let e = 2.71828182845904523536028747135266250 as u128;
    let n = e ** &exponent;
    let x_in_y_in_k_c_add = n.checked_add(c)?; 
    let x_in_y_in_k_c_sub = n.checked_sub(c)?;
    
    let x_in_y_in_div = source_amount.checked_div(destination_amount)?;
    let k_mul_x_y_ins = k.checked_mul(x_in_y_in_div)?.sqrt();
    let end_x_sum_num = k_mul_x_y_ins.checked_mul(x_in_y_in_k_c_add)?;
    let end_x_sum = end_x_sum_num.checked_div(x_in_y_in_k_c_sub)?;
    let end_y_sum = k.checked_div(end_x_sum)?;

    let x_total = source_amount.checked_add(swap_source_amount)?;
    let y_total = destination_amount.checked_add(swap_destination_amount)?;
    let x_out = x_total.checked_sub(end_x_sum)?;
    let y_out = y_total.checked_sub(end_y_sum)?;

    let source_amount_swapped_rhs = swap_destination_amount.checked_div(destination_amount)?;
    let destination_amount_swapped_rhs = swap_source_amount.checked_div(source_amount)?;
    
    let source_amount_swapped = x_out.checked_mul(source_amount_swapped_rhs)?;
    let destination_amount_swapped = y_out.checked_mul(destination_amount_swapped_rhs)?;
    
    Some(SwapWithoutFeesResult {
        source_amount_swapped, 
        destination_amount_swapped, 
    })
}


// advance twamm
fn process_virtual_trades(
    destination_amount: u128, // y_in
    source_amount: u128, // x_in
    swap_source_amount: u128, // x
    swap_destination_amount: u128, // y
    last_block_seen: u128, 
    block_number : u128) 
    -> Option<u128> {
    for _block in last_block_seen..block_number {
        infinitesimal(destination_amount, source_amount, swap_source_amount, swap_destination_amount);
    let _last_block_seen = block_number;
    }
    Some(last_block_seen)
}

#[warn(missing_docs)]
pub fn do_arb(
    destination_amount: u128, // y_in
    source_amount: u128, // x_in
    swap_source_amount: u128, // x
    swap_destination_amount: u128, // y
    last_block_seen : u128,
    block_number: u128,
    true_destination_price: u128,
) {
    let result = find_arb(swap_source_amount, swap_destination_amount, true_destination_price).unwrap();
    let x_to_spend = result.source_amount_swapped;
    let y_to_spend = result.destination_amount_swapped;

    // trade with internal amm
    // advance twamm
    let _last_block_seen = process_virtual_trades(destination_amount, source_amount, swap_source_amount, swap_destination_amount, last_block_seen, block_number);
    swap(source_amount, x_to_spend, y_to_spend);
}

#[warn(missing_docs)]
pub fn find_arb(
    swap_source_amount: u128, // x
    swap_destination_amount: u128, // y
    true_destination_price: u128,
) -> Option<SwapWithoutFeesResult> {
    let destination_amount_swapped;
    let source_amount_swapped;
    let instantaneous_destination_price = swap_source_amount.checked_div(swap_destination_amount)?;
    
    if true_destination_price > instantaneous_destination_price {
        let exp = 1/2 as u32;
        let exp_sub = 1 as u32;
        let exponent = exp.checked_sub(exp_sub)?;
        let marginal_swap_price_lhs = true_destination_price.checked_mul(swap_destination_amount)?;
        let marginal_swap_price =  marginal_swap_price_lhs.checked_div(swap_source_amount)?;
        let optimize_rhs = marginal_swap_price.checked_pow(exponent)?;
        let profit = swap_source_amount.checked_mul(optimize_rhs)?;
    
        if profit > 0 {
            source_amount_swapped = profit;
        }
        else {
            source_amount_swapped = 0;
        }
        destination_amount_swapped = 0;
    }
    else if true_destination_price < instantaneous_destination_price {
        let exp = 1/2 as u32;
        let exp_sub = 1 as u32;
        let exponent = exp.checked_sub(exp_sub)?;
        let marginal_swap_price_lhs = (1/true_destination_price).checked_mul(swap_source_amount)?;
        let marginal_swap_price = marginal_swap_price_lhs.checked_div(swap_destination_amount)?;
        let optimize_rhs = marginal_swap_price.checked_pow(exponent)?;
        let profit = swap_destination_amount.checked_mul(optimize_rhs)?;
        if profit > 0 {
            destination_amount_swapped = profit;
        }
        else {
           destination_amount_swapped = 0;
        }    
        source_amount_swapped = 0;
    }
    else {
        source_amount_swapped = 0;
        destination_amount_swapped = 0;
    }

    Some(SwapWithoutFeesResult {
        source_amount_swapped, 
        destination_amount_swapped, 
    })
}

/// Get the amount of trading tokens for the given amount of pool tokens,
/// provided the total trading tokens and supply of pool tokens.
///
/// The constant product implementation is a simple ratio calculation for how many
/// trading tokens correspond to a certain number of pool tokens
pub fn pool_tokens_to_trading_tokens(
    pool_tokens: u128,
    pool_token_supply: u128,
    swap_token_a_amount: u128,
    swap_token_b_amount: u128,
    round_direction: RoundDirection,
) -> Option<TradingTokenResult> {
    let mut token_a_amount = pool_tokens
        .checked_mul(swap_token_a_amount)?
        .checked_div(pool_token_supply)?;
    let mut token_b_amount = pool_tokens
        .checked_mul(swap_token_b_amount)?
        .checked_div(pool_token_supply)?;
    let (token_a_amount, token_b_amount) = match round_direction {
        RoundDirection::Floor => (token_a_amount, token_b_amount),
        RoundDirection::Ceiling => {
            let token_a_remainder = pool_tokens
                .checked_mul(swap_token_a_amount)?
                .checked_rem(pool_token_supply)?;
            // Also check for 0 token A and B amount to avoid taking too much
            // for tiny amounts of pool tokens.  For example, if someone asks
            // for 1 pool token, which is worth 0.01 token A, we avoid the
            // ceiling of taking 1 token A and instead return 0, for it to be
            // rejected later in processing.
            if token_a_remainder > 0 && token_a_amount > 0 {
                token_a_amount += 1;
            }
            let token_b_remainder = pool_tokens
                .checked_mul(swap_token_b_amount)?
                .checked_rem(pool_token_supply)?;
            if token_b_remainder > 0 && token_b_amount > 0 {
                token_b_amount += 1;
            }
            (token_a_amount, token_b_amount)
        }
    };
    Some(TradingTokenResult {
        token_a_amount,
        token_b_amount,
    })
}


/// Get the amount of pool tokens for the deposited amount of token A or B.
///
/// The constant product implementation uses the Balancer formulas found at
/// <https://balancer.finance/whitepaper/#single-asset-deposit>, specifically
/// in the case for 2 tokens, each weighted at 1/2.
pub fn deposit_single_token_type(
    source_amount: u128,
    swap_token_a_amount: u128,
    swap_token_b_amount: u128,
    pool_supply: u128,
    trade_direction: TradeDirection,
    round_direction: RoundDirection,
) -> Option<u128> {
    let swap_source_amount = match trade_direction {
        TradeDirection::AtoB => swap_token_a_amount,
        TradeDirection::BtoA => swap_token_b_amount,
    };
    let swap_source_amount = PreciseNumber::new(swap_source_amount)?;
    let source_amount = PreciseNumber::new(source_amount)?;
    let ratio = source_amount.checked_div(&swap_source_amount)?;
    let one = PreciseNumber::new(1)?;
    let base = one.checked_add(&ratio)?;
    let root = base.sqrt()?.checked_sub(&one)?;
    let pool_supply = PreciseNumber::new(pool_supply)?;
    let pool_tokens = pool_supply.checked_mul(&root)?;
    match round_direction {
        RoundDirection::Floor => pool_tokens.floor()?.to_imprecise(),
        RoundDirection::Ceiling => pool_tokens.ceiling()?.to_imprecise(),
    }
}

/// Get the amount of pool tokens for the withdrawn amount of token A or B.
///
/// The constant product implementation uses the Balancer formulas found at
/// <https://balancer.finance/whitepaper/#single-asset-withdrawal>, specifically
/// in the case for 2 tokens, each weighted at 1/2.
pub fn withdraw_single_token_type_exact_out(
    source_amount: u128,
    swap_token_a_amount: u128,
    swap_token_b_amount: u128,
    pool_supply: u128,
    trade_direction: TradeDirection,
    round_direction: RoundDirection,
) -> Option<u128> {
    let swap_source_amount = match trade_direction {
        TradeDirection::AtoB => swap_token_a_amount,
        TradeDirection::BtoA => swap_token_b_amount,
    };
    let swap_source_amount = PreciseNumber::new(swap_source_amount)?;
    let source_amount = PreciseNumber::new(source_amount)?;
    let ratio = source_amount.checked_div(&swap_source_amount)?;
    let one = PreciseNumber::new(1)?;
    let base = one.checked_sub(&ratio)?;
    let root = one.checked_sub(&base.sqrt()?)?;
    let pool_supply = PreciseNumber::new(pool_supply)?;
    let pool_tokens = pool_supply.checked_mul(&root)?;
    match round_direction {
        RoundDirection::Floor => pool_tokens.floor()?.to_imprecise(),
        RoundDirection::Ceiling => pool_tokens.ceiling()?.to_imprecise(),
    }
}

/// Calculates the total normalized value of the curve given the liquidity
/// parameters.
///
/// The constant product implementation for this function gives the square root of
/// the Uniswap invariant.
pub fn normalized_value(
    swap_token_a_amount: u128,
    swap_token_b_amount: u128,
) -> Option<PreciseNumber> {
    let swap_token_a_amount = PreciseNumber::new(swap_token_a_amount)?;
    let swap_token_b_amount = PreciseNumber::new(swap_token_b_amount)?;
    swap_token_a_amount
        .checked_mul(&swap_token_b_amount)?
        .sqrt()
}

impl CurveCalculator for TimeWeightedCurve {
    /// Constant product swap ensures x * y = constant
    fn swap_without_fees(
        &self,
        source_amount: u128,
        swap_source_amount: u128,
        swap_destination_amount: u128,
        _trade_direction: TradeDirection,
    ) -> Option<SwapWithoutFeesResult> {
        swap(source_amount, swap_source_amount, swap_destination_amount)
    }

    /// The constant product implementation is a simple ratio calculation for how many
    /// trading tokens correspond to a certain number of pool tokens
    fn pool_tokens_to_trading_tokens(
        &self,
        pool_tokens: u128,
        pool_token_supply: u128,
        swap_token_a_amount: u128,
        swap_token_b_amount: u128,
        round_direction: RoundDirection,
    ) -> Option<TradingTokenResult> {
        pool_tokens_to_trading_tokens(
            pool_tokens,
            pool_token_supply,
            swap_token_a_amount,
            swap_token_b_amount,
            round_direction,
        )
    }

    /// Get the amount of pool tokens for the deposited amount of token A or B.
    fn deposit_single_token_type(
        &self,
        source_amount: u128,
        swap_token_a_amount: u128,
        swap_token_b_amount: u128,
        pool_supply: u128,
        trade_direction: TradeDirection,
    ) -> Option<u128> {
        deposit_single_token_type(
            source_amount,
            swap_token_a_amount,
            swap_token_b_amount,
            pool_supply,
            trade_direction,
            RoundDirection::Floor,
        )
    }

    fn withdraw_single_token_type_exact_out(
        &self,
        source_amount: u128,
        swap_token_a_amount: u128,
        swap_token_b_amount: u128,
        pool_supply: u128,
        trade_direction: TradeDirection,
    ) -> Option<u128> {
        withdraw_single_token_type_exact_out(
            source_amount,
            swap_token_a_amount,
            swap_token_b_amount,
            pool_supply,
            trade_direction,
            RoundDirection::Ceiling,
        )
    }

    fn normalized_value(
        &self,
        swap_token_a_amount: u128,
        swap_token_b_amount: u128,
    ) -> Option<PreciseNumber> {
        normalized_value(swap_token_a_amount, swap_token_b_amount)
    }

    fn validate(&self) -> Result<(), SwapError> {
        Ok(())
    }
}

/// IsInitialized is required to use `Pack::pack` and `Pack::unpack`
impl IsInitialized for TimeWeightedCurve {
    fn is_initialized(&self) -> bool {
        true
    }
}

impl Sealed for TimeWeightedCurve {}
impl Pack for TimeWeightedCurve {
    const LEN: usize = 0;
    fn pack_into_slice(&self, output: &mut [u8]) {
        (self as &dyn DynPack).pack_into_slice(output);
    }

    fn unpack_from_slice(_input: &[u8]) -> Result<TimeWeightedCurve, ProgramError> {
        Ok(Self {})
    }
}

impl DynPack for TimeWeightedCurve {
    fn pack_into_slice(&self, _output: &mut [u8]) {}
}