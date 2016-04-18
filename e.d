module e;
import std.ascii;
import std.algorithm;
import std.range;
import std.conv;
import std.stdio;
import std.functional;
import std.typecons;
import std.bigint;
import std.typetuple;
import std.datetime;
import std.string : strip;

void main(string[] args) {
	auto id = args.length < 2 ? 0 : args[1].to!uint;
	foreach (f; __traits(allMembers, e)) {
		static if (f.startsWith("e") && f[1 .. $].all!isDigit) {
			enum fid = f[1 .. $].to!uint;
			if (id == 0) {
				writeln(" ", f);
				writeln("  ", mixin(f));
			}
			if (id == fid) {
				writeln(mixin(f));
			}
		}
	}
}

//apply function to all elements of a tuple
auto apply(alias F = "a", T)(T t) {
	enum mixer = iota(0, T.length).map!(a => "unaryFun!F(t[" ~ a.to!string ~ "]),").joiner.array;
	mixin("return tuple(" ~ mixer ~ ");");
}

//given an aliasSeq of ranges, returns a range that contains all ranges
auto only2(T...)(T t) {
	static struct Range {
		T tup;
		size_t index;

		void popFront() {
			index++;
		}

		@property auto front() {
			return chooseAmong(index, tup);
		}

		@property bool empty() {
			return index >= T.length;
		}
	}

	return Range(t);
}

auto sinkReduce(alias fun, alias called, T, A...)(T seed, A args) {
	called!((a) { seed = binaryFun!fun(seed, a); })(args);
	return seed;
}

auto dropN(R)(R range, size_t index) {
	return range.save.take(index).chain(range.save.drop(index + 1));
}
//finds where a range starts repeating and counts the diff in elements
auto repeatCount(R)(R range) {
	auto start = range.save;
	foreach (i, e; range.drop(1).enumerate(1)) {
		foreach (ri, re; start.save.take(i).enumerate) {
			if (re == e) {
				return i - ri;
			}
		}
	}
	assert(0);
}

auto stateRecurrence(alias fun, T...)(T args) {
	auto state = args[0 .. 1];
	auto init = args[1 .. $];
	return recurrence!((a, n) => fun(a, n, state))(init);
}

template mapMax(alias fun) {
	auto mapMax(TA, TB)(TA a, TB b) {
		if (unaryFun!fun(b) > unaryFun!fun(a)) {
			return b;
		}
		return a;
	}
}

//given a range and a range of ints,returns a range of ranges of 
auto taker(T, R)(T t, R r) {
	static struct Range {
		T source;
		R ints;
		void popFront() {
			source.popFrontN(ints.front);
			ints.popFront;
		}

		@property auto front() {
			return source.save.take(ints.front);
		}

		@property bool empty() {
			return source.empty;
		}
	}

	return Range(t, r);
}

auto parallel(R, T)(R range, T start) {
	return zip(start.only.chain(range), range);
}

//shh global state
ulong[] primesCache = [2];
auto primes() {
	static struct Range {
		size_t index;

		void popFront() {
			if (primesCache.length - 1 == index) {
				ulong np = primesCache[$ - 1] + 1;
				loop: foreach (p; primesCache) {
					if (np % p == 0) {
						np++;
						goto loop;
					}
				}
				primesCache ~= np;
			}
			index++;
		}

		@property auto front() {
			return primesCache[index];
		}

		enum empty = false;

		@property auto save() {
			return this;
		}
	}

	return Range();
}

auto primeFactors(T)(T t) {
	static struct Range(P) {
		T num;
		P primeGen;
		T front;
		bool empty;
		void popFront() {
			front = primeGen.front;
			if (front > num) {
				empty = true;
				return;
			}
			if (num % front == 0) {
				num /= front;
				return;
			}
			primeGen.popFront;
			popFront;
		}

		@property auto save() {
			return typeof(this)(num, primeGen.save, front, empty);
		}
	}

	static auto range(P)(T num, P primeGen) {
		return Range!P(num, primeGen);
	}

	return range(t, primes.map!(to!T)).drop(1);
}

auto countDigits(uint base = 10, T)(T t) {
	if (t < base) {
		return 1;
	}
	return countDigits!base(t / base) + 1;
}

auto isPalindrome(uint base = 10, T)(T t) {
	auto digits = t.countDigits!base;
	foreach (i; 0 .. digits / 2) {
		if (t / base ^^ i % base != t / base ^^ (digits - i - 1) % base) {
			return false;
		}
	}
	return true;
}

auto factorsTuple(T)(T t) {
	static struct Range {
		T num;
		T cur;
		Tuple!(T, T) front;
		void popFront() {
			cur++;
			while (!empty && num % cur != 0) {
				cur++;
			}
			front = tuple(cur, num / cur);
		}

		@property bool empty() {
			return num < cur * cur;
		}

		@property auto save() {
			return this;
		}
	}

	return Range(t, 1, tuple(cast(T) 1, t));
}

auto factors(T)(T t) {
	return factorsTuple(t).map!(a => a.expand.only).joiner.group.map!"a[0]"; //group.map!... revomes corner cases of perfect squares
}

auto gcd(T)(T a, T b) {
	if (b == 0) {
		return a;
	}
	return gcd(b, a % b);
}

auto lcm(T)(T a, T b) {
	return a / gcd(a, b) * b;
}

auto charTo(T)(dchar c) {
	assert(c >= '0' && c <= '9');
	return cast(T)(c - '0');
}

auto digits(T)(T t) {
	assert(t >= 0);
	return t.to!string.map!(charTo!ubyte);
}

auto wordedNum(alias sink, T)(T t) {
	if (t < 20) {
		sink(["zero", "one", "two", "three", "four", "five", "six", "seven",
			"eight", "nine", "ten", "eleven", "twelve", "thirteen", "fourteen",
			"fifteen", "sixteen", "seventeen", "eighteen", "nineteen"][t]);
		return;
	}
	auto num = 20;
	foreach (numStr; ["twenty", "thirty", "forty", "fifty", "sixty",
			"seventy", "eighty", "ninety"]) {
		if (t < num + 10) {
			sink(numStr);
			if (t != num) {
				wordedNum!sink(t - num);
			}
			return;
		}
		num += 10;
	}
	foreach (i; 1 .. 10) {
		if (t < i * 100 + 100) {
			wordedNum!sink(i);
			sink("hundred");
			if (t != i * 100) {
				sink("and");
				wordedNum!sink(t - i * 100);
			}
			return;
		}
	}
	foreach (i; 1 .. 10) {
		if (t < i * 1000 + 1000) {
			wordedNum!sink(i);
			sink("thousand");
			if (t != i * 1000) {
				wordedNum!sink(t - i * 1000);
			}
			return;
		}
	}

}

const(int)[] maxPathSum(Tri)(Tri triangle) {
	if (triangle.length == 1) {
		return triangle[0];
	}
	auto sums = maxPathSum(triangle[1 .. $]);
	auto col = triangle[0];
	return zip(zip(col, sums).map!(a => a[0] + a[1]), zip(col,
		sums.drop(1)).map!(a => a[0] + a[1])).map!(a => a.expand.max).array;
}

auto isPrime(T)(T t) {
	return t > 1 && t.primeFactors.drop(1).empty;
}

auto e1() {
	return iota(1, 1000).filter!"a % 3 == 0 || a % 5 == 0".reduce!"a + b";
}

auto e2() {
	return recurrence!"a[n - 1] + a[n - 2]"(1, 2).until!"a >= 4000000".filter!"a % 2 == 0".reduce!"a + b";
}

auto e3() {
	return primeFactors(600851475143).reduce!"b";
}

auto e4() {
	return iota(100, 1000).map!(a => zip(a.repeat, iota(100, 1000))).joiner.map!"a[0] * a[1]".filter!isPalindrome.reduce!max;
}

auto e5() {
	return iota(1, 21).reduce!lcm;
}

auto e6() {
	return iota(1, 101).reduce!"a + b" ^^ 2 - iota(1, 101).map!"a * a".reduce!"a + b";
}

auto e7() {
	return primes.drop(10000).front;
}

auto e8() {
	enum int[] nums = import("p008.txt").strip.splitter('\n').joiner.chunks(1).map!(
			a => a.front.charTo!int).array;
	return nums.map!(a => a.to!ulong).repeat.enumerate.map!(a => a[1].drop(a[0]).take(13)).until!"a.empty".map!(
		a => a.reduce!"a * b").reduce!max;
}

auto e9() {
	return iota(1000 / 3, 1000).map!(a => zip(iota(1,
		(1000 - a) / 2 + 1).retro.drop((1000 - a) % 2 == 0 ? 1 : 0),
		iota((1001 - a) / 2, a).drop((1000 - a) % 2 == 0 ? 1 : 0), a.repeat)).joiner.filter!"a[0] ^^ 2 + a[1] ^^ 2 == a[2] ^^ 2"
		.front.expand.only.reduce!"a * b";
}

auto e10() {
	return primes.until!"a >= 2000000".reduce!"a + b";
}

auto e11() {
	enum nums = import("p011.txt").strip.splitter('\n').map!(
			a => a.splitter(' ').map!(to!int).array).array;
	static auto up(T)(T t) {
		return t.repeat.enumerate.map!(a => tuple(a[1][0], a[1][1] - cast(int) a[0])).until!"a[1] == 0"(
			OpenRight.no);
	}

	static auto down(T)(T t) {
		return t.repeat.enumerate.map!(a => tuple(a[1][0], a[1][1] + cast(int) a[0])).until!"a[1] == 19"(
			OpenRight.no);
	}

	static auto left(T)(T t) {
		return t.repeat.enumerate.map!(a => tuple(a[1][0] - cast(int) a[0], a[1][1])).until!"a[0] == 0"(
			OpenRight.no);
	}

	static auto right(T)(T t) {
		return t.repeat.enumerate.map!(a => tuple(a[1][0] + cast(int) a[0], a[1][1])).until!"a[0] == 19"(
			OpenRight.no);
	}

	static auto upLeft(T)(T t) {
		return t.repeat.enumerate.map!(a => tuple(a[1][0] - cast(int) a[0], a[1][1] - cast(int) a[0])).until!"a[0] == 0 || a[1] == 0"(
			OpenRight.no);
	}

	static auto upRight(T)(T t) {
		return t.repeat.enumerate.map!(a => tuple(a[1][0] + cast(int) a[0], a[1][1] - cast(int) a[0])).until!"a[0] == 19 || a[1] == 0"(
			OpenRight.no);
	}

	static auto downLeft(T)(T t) {
		return t.repeat.enumerate.map!(a => tuple(a[1][0] - cast(int) a[0], a[1][1] + cast(int) a[0])).until!"a[0] == 0 || a[1] == 19"(
			OpenRight.no);
	}

	static auto downRight(T)(T t) {
		return t.repeat.enumerate.map!(a => tuple(a[1][0] + cast(int) a[0], a[1][1] + cast(int) a[0])).until!"a[0] == 19 || a[1] == 19"(
			OpenRight.no);
	}

	return iota(0, 20).map!(a => zip(a.repeat, iota(0, 20)).map!(a => adjoin!(up,
		down, left, right, upLeft, upRight, downLeft, downRight)(a).apply!(
		b => b.take(4).map!(c => nums[c[1]][c[0]]).reduce!"a * b").expand.only)).joiner.joiner.reduce!max;
}

auto e12() {
	return recurrence!"a[n - 1] + n"(0).until!(a => a.factors.count > 500)(OpenRight.no).reduce!"b";
}

auto e13() {
	enum nums = import("p013.txt").strip.splitter('\n').map!(a => BigInt(a)).array;
	return nums.reduce!"a + b".digits.take(10).map!(to!ulong).reduce!"a * 10 + b";
}

auto e14() {
	return iota(1, 1000000uL).map!(
		a => a.recurrence!"a[n - 1] % 2 == 0 ? a[n - 1] / 2 : a[n - 1] * 3 + 1".until!"a == 1"(
		OpenRight.no)).reduce!(mapMax!(count)).front;
}

auto e15() {
	//todo find a faster implentation
	static ulong l(ulong a, ulong b) {
		if (a == 0 || b == 0) {
			return 1;
		}
		return memoize!(l, 1024)(a - 1, b) + memoize!(l, 1024)(a, b - 1);
	}

	return l(20, 20);
}

auto e16() {
	return (BigInt(2) ^^ 1000).digits.map!(to!ulong).reduce!"a + b";
}

auto e17() {
	return iota(1, 1001).map!(a => sinkReduce!("a + cast(int)b.length", wordedNum)(0,
		a)).reduce!"a + b";
}

auto e18() {
	enum triangle = import("p018.txt").strip.splitter('\n').map!(
			a => a.splitter(' ').map!(to!int).array).array;
	return maxPathSum(triangle)[0];
}

auto e19() {
	//not cheating
	return iota(1901, 2001).map!(a => zip(a.repeat, iota(1, 13)).map!(b => Date(b[0],
		b[1], 1))).joiner.filter!(a => a.dayOfWeek == DayOfWeek.sun).count;
}

auto e20() {
	return recurrence!"a[n - 1] * n"(BigInt(1)).drop(1).take(100).reduce!"b".digits.map!(to!int).reduce!"a + b";
}

auto e21() {
	return iota(2, 10000).filter!((a) {
		auto f = a.factors.dropN(1).reduce!"a + b";
		return f != a && f < 10000 && f.factors.dropN(1).reduce!"a + b" == a;
	}).reduce!"a + b";
}

auto e22() {
	enum string[] names = mixin("[" ~ import("p022_names.txt").strip ~ "]");
	return names.sort.map!(a => a.map!"a - 'A' + 1".reduce!"a + b").enumerate(1).map!"a[0] * cast(ulong)(a[1])".reduce!"a + b";
}

auto e23() {
	auto nums = iota(2, int.max).filter!(a => a.factors.dropN(1).reduce!"a + b" > a).until!"a / 2 > 28123".array;
	//todo find faster way to sort
	auto sums = nums.enumerate.map!(a => zip(a[1].repeat, iota(0, a[0] + 1).map!(a => nums[a]))).joiner.map!"a[0] + a[1]"
		.array.sort;
	return sums.parallel(0).map!(a => iota(a[0] + 1, a[1])).joiner.until!"a > 28124".reduce!"a + b";
}

auto e24() {
	ulong[10] buffer;
	iota(0, cast(ulong) buffer.length).copy(buffer[]);
	return buffer[].repeat.tee!(a => a.nextPermutation).drop(999999).front.reduce!"a * 10 + b";
}

auto e25() {
	return recurrence!"a[n - 2] + a[n - 1]"(BigInt(1), BigInt(1)).until!(a => a.countDigits == 1000)(
		OpenRight.no).count;
}

auto e26() {
	return iota(2, 1000).map!(x => stateRecurrence!((a, n, s) => a[n - 1] * 10 % s)(x,
		1).repeatCount).enumerate(2).reduce!(mapMax!"a[1]")[0];
}

auto e27() {
	static auto poly(long a, long b) {
		return iota(0, long.max).map!(x => x ^^ 2 + a * x + b);
	}

	return iota(-999, 1000).map!(a => zip(a.repeat, primes.until!"a >= 1000")).joiner.reduce!(
		mapMax!(a => poly(a.expand).until!(not!isPrime).count)).to!(Tuple!(long, long)).reduce!"a * b";
}

auto e28() {
	return iota(1, uint.max).taker(iota(1, uint.max).map!(a => (a * 2).repeat(4)).joiner).map!"a.front".take(
		1001 * 2 - 1).reduce!"a + b";
}

auto e29() {
	//todo find faster way to sort
	return iota(2, 101).map!(a => zip(a.repeat, iota(2, 101))).joiner.map!(a => BigInt(a[0]) ^^ a[1]).array.sort.group
		.map!"a[0]".count;
}

auto e30() {
	//10 ^ 6 is a rough estimate of the upper bound
	return iota(2, 10 ^^ 6).filter!(a => a == a.digits.map!"a ^^ 5".reduce!"a + b").reduce!"a + b";
}

auto e31() {
	auto combinations(T...)(uint c) {
		static if (T.length == 0) {
			return 1;
		} else {
			return iota(0, c / T[0] + 1).retro.map!(a => c - a * T[0]).map!(
				combinations!(T[1 .. $])).reduce!"a + b";
		}
	}

	return combinations!(200, 100, 50, 20, 10, 5, 2)(200);
}
