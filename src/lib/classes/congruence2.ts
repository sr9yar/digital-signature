import {
  getPowerOfTwoAndMultiplicator,
  modulo,
  modulo2,
  range,
  tt,
} from '../utility';

import { LoggerType } from '../types/logger.type';
import { logger } from './logger';

import { LargePowerModulo } from './large-power-modulo';
import { LegendreSymbol } from './legendre-symbol';
import { EuclideanAlgorithm } from './euclidean-algorithm';



// https://math.stackexchange.com/questions/1118753/how-to-solve-second-order-congruence-equation-if-modulo-is-not-a-prime-number


// 
// second degree congruent equation 
//
// x² ≡ b (mod m)
// finds x
// 

export class Congruence2 {

  logger: LoggerType = logger;

  // ========================
  public a: number = 420;
  public p: number = 1049;
  // ========================


  // result
  public result: number[] = [];


  constructor(a?: number, p?: number) {
    if (typeof a === 'number') {
      this.a = a;
    }
    if (typeof p === 'number') {
      this.p = p;
    }
  }

  /**
   * Calc
   * 
   * @returns 
   */
  calc(a?: number, p?: number): number[] {

    a = a ?? this.a;
    p = p ?? this.p;

    this.logger.log(`Уравнение x² ≡ ${a}(mod ${p}). a=${a}, p=${p}. Находим х.`);

    // Step 1
    this.logger.log(`Шаг 1. Вычисляем символ Лежандра.`, 'color:blue');
    this.logger.log(`${a}/${p} = ${a}(mod ${p})`);

    const ls = new LegendreSymbol(a, p);
    const legendre = ls.calc(a, p);

    if (legendre === 1) {
      this.logger.log(`Символ Лежандра равен 1 значит корни есть.`);
    } else {
      this.logger.log(`Символ Лежандра равен -1 значит корней нет.`);
      this.logger.log(`Решение окончено.`);
      return [];
    }

    this.logger.log(`Шаг 2. Найти целое b такое что (b/p) = -1.`, 'color:blue');

    const bValues = range(p);
    bValues[0] = -1;
    let b: number = -1;
    for (let i = 0; i < bValues.length; i++) {
      b = bValues[i];
      const ls = new LegendreSymbol(b, p);
      const legendre = ls.calc();
      if (legendre === -1) {
        this.logger.log(`b=${b} Подходит.`);
        break;
      }
      this.logger.log(`b=${b} Не подходит.`);

    }

    this.logger.log(`Значение найдено b=${b}.`);
    this.logger.log(`Шаг 3. представить p-1=(2^s)t где t - нечетное число.`, 'color:blue');

    const [s, t] = getPowerOfTwoAndMultiplicator(p - 1);
    this.logger.log(`${p}-1 = 2^${s} * ${t} → s=${s}, t=${t}`);

    this.logger.log(`Шаг 4. Вычислить a⁻¹ mod p по расширенному алгоритму Евклида.`, 'color:blue');

    // Deprecated: const euclid = this.euclidExtendedService.calc(p, a);
    // Deprecated: this.euclidExtendedService.printResults();
    const euclid = new EuclideanAlgorithm(p, a);
    const eaResults = euclid.calc();

    // a^-1
    let a_1 = eaResults[2];
    if (a_1 < -1) {
      a_1 += p;
    }
    this.logger.log(`Значение найдено a⁻¹=${a_1}.`);

    this.logger.log(`Шаг 5. Вычислить C₀ ← b^t mod p ; r ← a (t+1)/2 mod p.`, 'color:blue');
    this.logger.log(`b=${b}, t=${t}, p=${p}.`);

    // check
    // 3 ^ 119 mod 953 = 797
    // 221 ^ 60 mod 953 = 256
    // https://www.boxentriq.com/code-breaking/modular-exponentiation
    this.logger.log(`Возводим ${b} в степень ${t} по модулю ${p}.`);

    // Deprecated: let [rr, kk, AA, bb] = getPowerMod(t, b, p);
    const largeExp = new LargePowerModulo(b, t, p);
    const results = largeExp.printResults();
    let [rr, kk, AA, bb] = results;

    this.logger.log(`${kk.join('\t')}`, 'color:yellow');
    this.logger.log(`${AA.join('\t')}`, 'color:yellow');
    this.logger.log(`${bb.join('\t')}`, 'color:yellow');
    this.logger.log(`Ответ: ${rr}`, 'color:yellow');

    this.logger.log(`C₀ = ${b}^${t} mod ${p} = ${rr}`);
    let C0 = rr;
    //let C0 = 797;


    this.logger.log(`r=${a}^((${t}+1)/2) по модулю ${p}.`);

    const pow = (t + 1) / 2;
    this.logger.log(`Возводим ${a} в степень ${pow} по модулю ${p}.`);
    // Deprecated: [rr, kk, AA, bb] = getPowerMod(pow, a, p);
    const largeExp2 = new LargePowerModulo(a, pow, p);
    const results2 = largeExp2.printResults();
    [rr, kk, AA, bb] = results2;

    this.logger.log(`${kk.join('\t')}`, 'color:yellow');
    this.logger.log(`${AA.join('\t')}`, 'color:yellow');
    this.logger.log(`${bb.join('\t')}`, 'color:yellow');
    this.logger.log(`Ответ: ${rr}`, 'color:yellow');

    let r = rr;
    this.logger.log(`r = ${a}^((${t}+1)/2) mod ${p} = ${r}`);


    this.logger.log(`Шаг 6. i = 1...s-1 :`, 'color:blue');
    this.logger.log(`Цикл i от 1 до s-1, s=${s}`);
    // this.logger.log(`Шаг 6.1. di ← (r²a⁻¹)^(2-i-1) mod p`, 'color:blue');
    // this.logger.log(`Шаг 6.2. di = -1 (mod p)     r ← rC₀ mod p`, 'color:blue');
    // this.logger.log(`Шаг 6.3. C₀ ← C₀² mod p`, 'color:blue');


    //C0 *= 3;
    for (let i = 1; i < s; i++) {
      // a^-1 = a_1
      this.logger.log(`${tt(1)} `);
      this.logger.log(`${tt(1)}i=${i}`);
      this.logger.log(`${tt(1)}Шаг 6.1. d${i} ← ((r²a⁻¹)^2)^(s-i-1) mod p`);
      this.logger.log(`${tt(1)}d${i} = (${r}² * ${a_1}) ** (2 ** (${s} - ${i} - 1)) mod ${p}`);

      const pow = 2 ** (s - i - 1);
      // Шаг 6.1
      const di = (r ** 2 * a_1) ** pow;
      const di_mod_check = modulo2(di, p);
      const di_mod = di_mod_check.filter(m => (m === 1 || m === -1))[0];
      this.logger.log(`${tt(1)}d${i} = ${di_mod}`);

      this.logger.log(`${tt(1)}d${i}=${di}, d${i} mod p = ${di_mod_check}`, 'color:gray');
      if (di_mod === -1) {
        // Шаг 6.2
        this.logger.log(`${tt(1)}Шаг 6.2. выполняется так как d${i}=-1 (mod p) (d${i}=${di_mod}, r=${r}, C₀=${C0})`);
        this.logger.log(`${tt(1)}r = r * C₀ mod p = ${r} * ${C0} mod ${p}`);
        r = modulo(r * C0, p);
        this.logger.log(`${tt(1)}r = ${r}`);

      } else {
        this.logger.log(`${tt(1)}Шаг 6.2. не выполняется так как d${i}≠-1 (mod p) (d${i}=${di_mod})`);
      }
      this.logger.log(`${tt(1)}Шаг 6.3. C₀ ← C₀² mod p`);
      this.logger.log(`${tt(1)}C₀ = ${C0}² mod ${p}`);

      C0 = modulo(C0 ** 2, p);
      this.logger.log(`${tt(1)}C₀ = ${C0}`);
    }
    this.logger.log(`${tt(1)} `);

    this.logger.log(`Шаг 7. Вернуть (r; -r)`, 'color:blue');

    const check1 = modulo(r ** 2, p);
    const check2 = modulo(a, p);

    this.logger.log(`Проверка: (±r)² ≡ ${a} mod ${p}`);
    this.logger.log(`Проверка: (±${r})² ≡ ${a} mod ${p}`);
    this.logger.log(`Проверка: ${check1} = ${check2}`);

    // (r; -r)
    this.logger.log(`Ответ: (${+r}; ${-r})`, 'color:yellow');
    this.logger.log(` `);


    //  221
    //  953
    // ответ 255

    this.result = [+r, -r];
    return [+r, -r];
  }



  /**
   * Print result
   */
  printResults(): void {
    this.logger.log(`Result: ${this.result}`, 'color:cyan');
  }



  /**
   * Run
   * @returns 
   */
  run() {
    this.calc(this.a, this.p);
    this.printResults();
    return this.result;
  }

}
