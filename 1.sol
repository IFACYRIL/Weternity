// SPDX-License-Identifier: MIT

pragma solidity 0.7.4;

library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     * - Subtraction cannot overflow.
     *
     * _Available since v2.4.0._
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     *
     * _Available since v2.4.0._
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        // Solidity only automatically asserts when dividing by 0
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     *
     * _Available since v2.4.0._
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

contract Context {
    // Empty internal constructor, to prevent people from mistakenly deploying
    // an instance of this contract, which should be used via inheritance.
    constructor () { }
    // solhint-disable-previous-line no-empty-blocks

    function _msgSender() internal view returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * This test is non-exhaustive, and there may be false-negatives: during the
     * execution of a contract's constructor, its address will be reported as
     * not containing a contract.
     *
     * IMPORTANT: It is unsafe to assume that an address for which this
     * function returns false is an externally-owned account (EOA) and not a
     * contract.
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies in extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        // According to EIP-1052, 0x0 is the value returned for not-yet created accounts
        // and 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 is returned
        // for accounts without code, i.e. `keccak256('')`
        bytes32 codehash;
        bytes32 accountHash = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        // solhint-disable-next-line no-inline-assembly
        assembly { codehash := extcodehash(account) }
        return (codehash != 0x0 && codehash != accountHash);
    }

    /**
     * @dev Converts an `address` into `address payable`. Note that this is
     * simply a type cast: the actual underlying value is not changed.
     *
     * _Available since v2.4.0._
     */
    function toPayable(address account) internal pure returns (address payable) {
        return address(uint160(account));
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     *
     * _Available since v2.4.0._
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-call-value
        (bool success, ) = recipient.call{value:amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }
}

/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for ERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value, "SafeERC20: decreased allowance below zero");
        callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves.

        // A Solidity high level call has three parts:
        //  1. The target address is checked to verify it contains contract code
        //  2. The call itself is made, and success asserted
        //  3. The return value is decoded, which in turn checks the size of the returned data.
        // solhint-disable-next-line max-line-length
        require(address(token).isContract(), "SafeERC20: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = address(token).call(data);
        require(success, "SafeERC20: low-level call failed");

        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}


interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);


    function mint(address account, uint amount) external;
    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor () {
        _owner = _msgSender();
        emit OwnershipTransferred(address(0), _owner);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(isOwner(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Returns true if the caller is the current owner.
     */
    function isOwner() public view returns (bool) {
        return _msgSender() == _owner;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public onlyOwner {
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     */
    function _transferOwnership(address newOwner) internal {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

contract ReentrancyGuard {

    /// @dev counter to allow mutex lock with only one SSTORE operation
    uint256 private _guardCounter = 1;

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * If you mark a function `nonReentrant`, you should also
     * mark it `external`. Calling one `nonReentrant` function from
     * another is not supported. Instead, you can implement a
     * `private` function doing the actual work, and an `external`
     * wrapper marked as `nonReentrant`.
     */
    modifier nonReentrant() {
        _guardCounter += 1;
        uint256 localCounter = _guardCounter;
        _;
        require(localCounter == _guardCounter);
    }
}

contract ELPDOTPOOL is Context, ReentrancyGuard, Ownable {
    using SafeMath for uint256;
    using SafeERC20 for IERC20;

    uint256 public epochStart;
    uint256 public epochLength = 1 days;
    bool public pause = true;
    IERC20 public lpt = IERC20(0xDae876044756B51E83b8BCECf810be56cfad05B1);
    IERC20 public ELP = IERC20(0xE3894CB9E92ca78524Fb6a30Ff072FA5E533c162);
    
    struct EpochdepositDetails {
        uint256 allPrevdepositTotals;
        uint256 currentdepositTotal;
    }

    struct UserDetails {
        uint256 lastLiquidityAddedEpochReference;
        uint256 lastEpochUpdate;
        uint256 lastClaimedTimestamp;
        mapping(uint256 => EpochdepositDetails) epochTotals;
    }

    modifier checkpause {
        require(pause == true, "pool reward stopped");
        _;
    }

    mapping(address => UserDetails) public userDeposit;

    mapping(uint256 => EpochdepositDetails) public epochAmounts;

    uint256 public lastEpochUpdate = 1;

    uint256 public fistEpochReward = 10000 * 1e18;
    mapping(uint256 => uint256) public epochReward;

    event addliquidity(address sender, uint256 amount);
    event getrewards(address sender, uint256 rewards);
    event removeliquidity(address sender, uint256 amount, uint256 remains, uint256 rewards);

    constructor () {
        epochStart = block.timestamp;
        epochReward[1] = fistEpochReward;
        for(uint256 i=2; i<100; i++) {
            epochReward[i] = epochReward[i-1].mul(99).div(100);
        }
    }

    function storeEpochReward(uint256 lastepoch, uint256 epochs) public onlyOwner {
        require(lastepoch >= 2, "must increase by first epoch reward");
        for(uint256 i=lastepoch; i< (lastepoch + epochs); i++) {
            epochReward[i] = epochReward[i-1].mul(99).div(100);
        }
    }

    function getEpochRewards(uint256 epoch) public view returns(uint256){
        return epochReward[epoch];
    }

    function getUsersDepositTotal(address _user) public view returns (uint256) {
        EpochdepositDetails memory latestdepositDetails =
        userDeposit[_user].epochTotals[
        userDeposit[_user].lastEpochUpdate
        ];

        uint256 depositTotal =
        _getEpochAmountIncludingCurrent(latestdepositDetails);
        return (depositTotal);
    }

    function getUserDepositShare(address _user) public view returns (uint256) {
        uint256 userDepositTotal = getUsersDepositTotal(_user);
        uint256 allPrevdepositTotals =
        epochAmounts[lastEpochUpdate].allPrevdepositTotals;

        uint256 overall =
        allPrevdepositTotals.add(
            epochAmounts[lastEpochUpdate].currentdepositTotal
        );
        if (overall == 0) {
            return 0;
        }
        return (userDepositTotal.mul(100).div(overall));
    }

    function getAllDeposit() public view returns (uint256) {
        uint256 allPrevdepositTotals =
        epochAmounts[lastEpochUpdate].allPrevdepositTotals;

        uint256 overall =
        allPrevdepositTotals.add(
            epochAmounts[lastEpochUpdate].currentdepositTotal
        );

        return overall;
    }

    function getUsersEpochTotals(uint256 epoch, address _user) public view  returns (
        uint256 currentdepositTotal,
        uint256 allPrevdepositTotals
    ) {
        EpochdepositDetails memory depositDetails =
        userDeposit[_user].epochTotals[epoch];
        return (
        depositDetails.currentdepositTotal,
        depositDetails.allPrevdepositTotals
        );
    }

    function getCurrentEpoch() public view returns (uint256) {
        return block.timestamp.sub(epochStart).div(epochLength).add(1);
    }

    function _getEpochToTimestamp(uint256 timestamp) public view returns (uint256){
        // ((timestamp - epochStart) / epochLength) + 1;
        return timestamp.sub(epochStart).div(epochLength).add(1);
    }

    function _getSecondsToEpochEnd(uint256 currentEpoch) public view returns (uint256) {
        // epochStart + (currentEpoch * epochLength) - block.timestamp
        uint256 epochEndTime = epochStart.add(currentEpoch.mul(epochLength));
        if (epochEndTime < block.timestamp) {
            return 0;
        } else {
            return epochEndTime.sub(block.timestamp);
        }
    }

    function _updateUserDetailsAndEpochAmounts(
        address _userAddress,
        uint256 _amount
    ) internal {
        // Get the current epoch
        uint256 currentEpoch = _getEpochToTimestamp(block.timestamp);

        UserDetails storage currentUser = userDeposit[_userAddress];

        if (currentUser.lastEpochUpdate == 0) {
            currentUser.lastLiquidityAddedEpochReference = currentEpoch;
            currentUser.lastClaimedTimestamp = block.timestamp;
        }
        uint256 usersTotal = _getEpochAmountIncludingCurrent(
            currentUser.epochTotals[currentUser.lastEpochUpdate]
        );
        if (usersTotal == 0) {
            uint256 lastClaimedEpoch = _getEpochToTimestamp(currentUser.lastClaimedTimestamp);
            if (lastClaimedEpoch > currentUser.lastEpochUpdate) {
                currentUser.lastClaimedTimestamp = block.timestamp;
            }
        }

        if (currentUser.lastEpochUpdate < currentEpoch) {
            uint256 allPrevdepositTotals =
            currentUser.epochTotals[currentUser.lastEpochUpdate]
            .allPrevdepositTotals;

            uint256 pulledForwardTotal =
            allPrevdepositTotals.add(
                currentUser.epochTotals[currentUser.lastEpochUpdate]
                .currentdepositTotal
            );

            currentUser.epochTotals[currentEpoch]
            .allPrevdepositTotals = pulledForwardTotal;

            currentUser.lastEpochUpdate = currentEpoch;
        }

        currentUser.epochTotals[currentEpoch]
        .currentdepositTotal = currentUser.epochTotals[currentEpoch]
        .currentdepositTotal
        .add(_amount);

        if (lastEpochUpdate < currentEpoch) {
            uint256 allPrevdepositTotals =
            epochAmounts[lastEpochUpdate].allPrevdepositTotals;

            uint256 overallPulledForwardTotal =
            allPrevdepositTotals.add(
                epochAmounts[lastEpochUpdate].currentdepositTotal
            );

            epochAmounts[currentEpoch]
            .allPrevdepositTotals = overallPulledForwardTotal;

            lastEpochUpdate = currentEpoch;
        }

        epochAmounts[currentEpoch].currentdepositTotal = epochAmounts[currentEpoch]
        .currentdepositTotal
        .add(_amount);
    }

    function addLiquidity(uint256 _amount) external  nonReentrant checkpause {
        require(_amount != 0, "Cannot add 0");
        require(
            lpt.allowance(_msgSender(), address(this)) >= _amount,
            "Need approve first"
        );
        require(
            lpt.balanceOf(_msgSender()) >= _amount,
            "Balance not enough"
        );

        lpt.safeTransferFrom(_msgSender(), address(this), _amount);
        _updateUserDetailsAndEpochAmounts(_msgSender(), _amount);
        
        emit addliquidity(_msgSender(), _amount);
    }

    function _getEpochClaimSeconds(
        uint256 epoch,
        uint256 currentEpoch,
        uint256 lastEpochClaimed,
        uint256 lastClaimedTimestamp
    ) public view returns (uint256) {
        if (epoch == currentEpoch) {
            //  block.timestamp - lastClaimedtimestamp
            if (lastEpochClaimed == currentEpoch) {
                return block.timestamp.sub(lastClaimedTimestamp);
            }
            // timestamp - startOfEpoch
            uint256 givenEpochStartTime = getGivenEpochStartTime(epoch);
            return block.timestamp.sub(givenEpochStartTime);

        } else if (lastEpochClaimed == epoch) {
            // the end of the given epoch - the lastClaimed timestmap
            uint256 givenEpochEndTime = getGivenEpochEndTime(epoch);
            return givenEpochEndTime.sub(lastClaimedTimestamp);
        }
        return epochLength;
    }

    function _getEpochAmountIncludingCurrent(
        EpochdepositDetails memory epochdepositDetails
    ) internal view returns (uint256) {
        return
        epochdepositDetails.allPrevdepositTotals.add(
            epochdepositDetails.currentdepositTotal
        );
    }

    function getRewardAmount(
        uint256 usersdepositTotal,
        uint256 overalldepositTotal,
        uint256 secondsToClaim,
        uint256 totalReward
    ) public view returns (uint256) {
        // totalReward * usersdepositTotal / overallEpochTotal
        uint256 totalEpochRewardShare =
        totalReward.mul(usersdepositTotal).div(overalldepositTotal);

        // totalEpochRewardShare * secondsToClaim / epochLength
        uint256 proportionalRewardShare =
        totalEpochRewardShare.mul(secondsToClaim).div(epochLength);

        // totalReward * (usersdepositTotal / overallEpochTotal) * (secondsToClaim / epochLength)
        return proportionalRewardShare;
    }

    function _calRewardShare(
        uint256 epoch,
        uint256 currentEpoch,
        uint256 lastEpochClaimed,
        uint256 lastClaimedTimestamp,
        uint256 usersdepositTotal,
        uint256 overalldepositTotal
    ) internal view returns (uint256) {
        uint256 claimSeconds =
        _getEpochClaimSeconds(
            epoch,
            currentEpoch,
            lastEpochClaimed,
            lastClaimedTimestamp
        );

        uint256 totalEpochRewards = epochReward[epoch];

        return
        getRewardAmount(
            usersdepositTotal,
            overalldepositTotal,
            claimSeconds,
            totalEpochRewards
        );
    }
    
    function getRewardAmounts(address _user) public view
    returns (uint256 rewardTotal, uint256 epochCheckpoint)
    {
        UserDetails storage currentUser = userDeposit[_user];

        if (currentUser.lastEpochUpdate == 0) {
            return (0,0);
        }

        uint256 currentEpoch = _getEpochToTimestamp(block.timestamp);

        uint256 lastEpochClaimed = _getEpochToTimestamp(currentUser.lastClaimedTimestamp);
        
        uint256 lastEpochRef = currentUser.lastLiquidityAddedEpochReference;
        if ( lastEpochRef < lastEpochClaimed) {
            lastEpochClaimed = lastEpochRef;
        }
        
        uint256 usersEpochTotal;
        uint256 overallEpochTotal;
        
        if (currentEpoch > lastEpochClaimed.add(100)) {
            epochCheckpoint = lastEpochClaimed.add(100);
        } else {
            epochCheckpoint = currentEpoch;
        }
        
        uint256 lastEpochUpdate_user  = currentUser.lastEpochUpdate;
        
        for (uint256 epoch = lastEpochClaimed; epoch <= epochCheckpoint; epoch++) {
            usersEpochTotal = _getEpochAmountIncludingCurrent(
                currentUser.epochTotals[lastEpochUpdate_user]);
            
            if (usersEpochTotal == 0) continue;
            
            overallEpochTotal = _getEpochAmountIncludingCurrent(epochAmounts[epoch]);
            if (overallEpochTotal == 0) {
                overallEpochTotal = _getEpochAmountIncludingCurrent(epochAmounts[lastEpochUpdate]);
            }

            uint256 epochRewardShare =
            _calRewardShare(
                epoch,
                currentEpoch,
                lastEpochClaimed,
                currentUser.lastClaimedTimestamp,
                usersEpochTotal,
                overallEpochTotal
            );
            
            rewardTotal = rewardTotal.add(epochRewardShare);
        }

        return (rewardTotal, epochCheckpoint);
    }

    function getRewards() public nonReentrant {
        UserDetails storage currentUser = userDeposit[_msgSender()];

        // require the user to actually have an deposit amount
        require (
            currentUser.lastEpochUpdate > 0,
            "User has no rewards to claim, as they have never added liquidity"
        );

        (
        uint256 allClaimableAmounts,
        uint256 epochCheckpoint
        ) = getRewardAmounts(_msgSender());
        
        // Update their last claim to now
        
        currentUser.lastLiquidityAddedEpochReference = epochCheckpoint;
        
        
        uint256 currentEpoch = _getEpochToTimestamp(block.timestamp);
        uint256 lastEpochClaimed = _getEpochToTimestamp(currentUser.lastClaimedTimestamp);
        if (currentEpoch > lastEpochClaimed.add(100)) {
            currentUser.lastClaimedTimestamp = (lastEpochClaimed.add(99).mul(epochLength) + epochStart);
        } else {
            currentUser.lastClaimedTimestamp = block.timestamp;
        }
        if (allClaimableAmounts == 0) {
            return;
        }

        ELP.safeTransfer(_msgSender(), allClaimableAmounts);
        emit getrewards(_msgSender(), allClaimableAmounts);
    }
    
    function removeLiquidity(uint256 _amount) public nonReentrant {
        UserDetails storage currentUser = userDeposit[_msgSender()];

        uint256 totaldeposit = getUsersDepositTotal(_msgSender());
        require(totaldeposit > 0, "total deposit need > 0");
        require(totaldeposit >= _amount, "total deposit need > remove amount");
        EpochdepositDetails storage latestdepositDetails =
        userDeposit[_msgSender()].epochTotals[
        userDeposit[_msgSender()].lastEpochUpdate
        ];
        
        (
        uint256 allClaimableAmounts,
        uint256 epochcheckpoint
        )  = getRewardAmounts(_msgSender());
        
        uint256 currentEpoch = _getEpochToTimestamp(block.timestamp);
        
        if (currentEpoch == lastEpochUpdate) {
            epochAmounts[lastEpochUpdate].currentdepositTotal = epochAmounts[lastEpochUpdate].currentdepositTotal
            .sub(latestdepositDetails.currentdepositTotal);

            epochAmounts[lastEpochUpdate].allPrevdepositTotals = epochAmounts[lastEpochUpdate].allPrevdepositTotals
            .sub(latestdepositDetails.allPrevdepositTotals);
        } else {
            epochAmounts[currentEpoch].allPrevdepositTotals = epochAmounts[lastEpochUpdate].allPrevdepositTotals
            .add(epochAmounts[lastEpochUpdate].currentdepositTotal)
            .sub(totaldeposit);
            epochAmounts[currentEpoch].currentdepositTotal = 0;
        }
        latestdepositDetails.allPrevdepositTotals = 0;
        latestdepositDetails.currentdepositTotal = 0;
        lastEpochUpdate = currentEpoch;
        currentUser.lastLiquidityAddedEpochReference = epochcheckpoint;
        // currentUser.lastEpochUpdate = 0;
        currentUser.lastClaimedTimestamp = block.timestamp;
        
        ELP.safeTransfer(_msgSender(), allClaimableAmounts);
        lpt.safeTransfer(_msgSender(), _amount);
        if (totaldeposit.sub(_amount) > 0) {
          _updateUserDetailsAndEpochAmounts(_msgSender(), totaldeposit.sub(_amount));  
        }
        emit removeliquidity(_msgSender(), _amount, allClaimableAmounts, totaldeposit.sub(_amount));
    }
    
    // one day per epoch, 365 epochs
    function getAPY() public view returns (uint256) {
        uint256 currentEpoch = getCurrentEpoch();
        uint256 totalReward;

        for (uint256 i = currentEpoch; i < (currentEpoch + 365); i++) {
            totalReward += epochReward[i];
        }

        uint256 overallEpochTotal =
        _getEpochAmountIncludingCurrent(
            epochAmounts[lastEpochUpdate]
        );

        if (overallEpochTotal == 0) {
            overallEpochTotal = 1 * 1e18;
        }
        uint256 totalAPY = totalReward.mul(100).div(overallEpochTotal);
        return totalAPY;
    }

    function getGivenEpochEndTime(uint256 epoch) public view returns (uint256) {
        return epochStart.add(epochLength.mul(epoch));
    }

    function getGivenEpochStartTime(uint256 epoch) public view returns (uint256) {
        return epochStart.add(epochLength.mul(epoch.sub(1)));
    }

    function withdrawRemains(uint256 amount) public onlyOwner {
        ELP.safeTransfer(_msgSender(), amount);
    }

    function pauseswitch(bool _pause) public onlyOwner {
        pause = _pause;
    }
    
    function withdrawOnly() public nonReentrant {
        uint256 totaldeposit = getUsersDepositTotal(_msgSender());
        require(totaldeposit > 0, "total deposit need > 0");
        
        EpochdepositDetails storage latestdepositDetails =
        userDeposit[_msgSender()].epochTotals[
        userDeposit[_msgSender()].lastEpochUpdate
        ];
        
        uint256 currentEpoch = _getEpochToTimestamp(block.timestamp);
        
        if (currentEpoch == lastEpochUpdate) {
            epochAmounts[lastEpochUpdate].currentdepositTotal = epochAmounts[lastEpochUpdate].currentdepositTotal
            .sub(latestdepositDetails.currentdepositTotal);

            epochAmounts[lastEpochUpdate].allPrevdepositTotals = epochAmounts[lastEpochUpdate].allPrevdepositTotals
            .sub(latestdepositDetails.allPrevdepositTotals);
        } else {
            epochAmounts[currentEpoch].allPrevdepositTotals = epochAmounts[lastEpochUpdate].allPrevdepositTotals
            .add(epochAmounts[lastEpochUpdate].currentdepositTotal)
            .sub(totaldeposit);
            epochAmounts[currentEpoch].currentdepositTotal = 0;
        }
        latestdepositDetails.allPrevdepositTotals = 0;
        latestdepositDetails.currentdepositTotal = 0;
        lastEpochUpdate = currentEpoch;
        lpt.safeTransfer(_msgSender(), totaldeposit);
    }
}
