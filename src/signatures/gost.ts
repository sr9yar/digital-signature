import {
  EuclideanAlgorithm,
} from '../lib/classes/euclidean-algorithm';
import {
  binToDec,
  decToBin,
  divideModulo,
  getAllSummands,
  getRandomInArray,
  getRandomNumber,
  isPrime,
  modulo2,
  moduloPositive,
  multiplyMod,
  plaintextToBinArray,
  primeFactors,
  slice,
  sub,
  sup,
} from '../lib/utility';
import {
  DigitalSignature,
} from './digital-signature';
import {
  // PRIME_NUMBERS,
  PRIME_NUMBERS_10K,
} from '../lib/constants';
import { LargePowerModulo, logger } from '../lib/classes';
import { Point } from '../lib/classes/point';



// GOST 34.10.-2012
// https://---------.io/n8EhjAf7HfhUtjBx3hj7yA



/**
 * GOST digital signautre class
 */
export class Gost extends DigitalSignature {

  logger = logger;

  // Блоки в десятичном представлении
  private inputBlocks: number[] = [];

  // параметры домена
  // Big prime number
  _p: number = 101; //
  // Эллиптическая кривая E задаваемая коэффицентами a и b  
  a = 4;
  //
  b = 1;
  // Целое число m - порядок группы точек эллиптической кривой E
  m = 1;
  // Просто число q - порядок циклической подгруппы группы точек 
  // эллиптической кривой E, m = nq, n ∈ ℕ
  q = 1;

  // Точки
  E: Point[] = [];

  //
  P: Map<number, Point> = new Map();

  // Ключ подписи - целое число d
  d: number = 1;

  // Ключ проверки подписи - точка эллиптической кривой Q=dP
  Q: Point;

  // Сообщение
  M: string = 'APR';

  // размер блока
  // l - битовая длина числа q
  l: number = 1;

  signatureA: number = 0;
  signatureE: number = 0;

  k: number = 0;

  r: number = 0;
  s: number = 0;

  // ЭЦП 
  signature: string;

  //  =====================

  hashFunction: Function = this.simpleHashFunction;


  // =====================

  // r obtained during verification
  vR: number = 0;
  // s obtained during verification
  vS: number = 0;
  //
  vA: number = 0;
  //
  vE: number = 0;
  //
  vHash: string = '';
  // e Inverse
  v: number = 0;

  Z1: number;
  Z2: number;

  //
  C: Point;

  R: number = 0;
  // =====================

  // show logs for adding pointss
  logAddingPoints: boolean = false;

  // log lists of points 
  logLongLists: boolean = false;

  // Verification result 
  signatureVerified: boolean = null;

  // Calculate all point of an elliptic curve
  calculateAllPoints: boolean = false;

  /**
   * Constructor
   */
  constructor(
    p?: number,
    a?: number,
    b?: number,
    logAddingPoints?: boolean,
  ) {
    super();

    if (logAddingPoints !== undefined) {
      this.logAddingPoints = !!logAddingPoints;
    }
    this.setDomainParameters(p, a, b);
  }

  /**
   * Set domain params
   */
  setDomainParameters(
    p?: number,
    a?: number,
    b?: number,
  ) {

    if (typeof p === 'number') {
      this._p = p;
    } else {
      this.generateP();
    }

    if (typeof a === 'number' && typeof b === 'number') {
      this.a = a;
      this.b = b;
    } else {
      this.generateAB();
    }

    // set m
    this.setM();

    // q
    this.generateQ();

    // Выбрать точку P
    this.selectPoint();
    this.defineHashFunction();
    this.defineD();
    this.defineQ();
  }


  /**
   * p setter
   */
  set p(value: number) {
    if (!isPrime(value)) {
      this.logger.warn(`Paramter p must be prime. p is ${value}. Aborting`);
      return;
    }
    this._p = value;
  }

  /**
   * 
   */
  get p(): number {
    return this._p;
  }



  /**
   * Choose random p
   */
  generateP() {
    this.logger.log(`1. [Определение параметров домена] `, 'color:yellow');

    const p = getRandomInArray(PRIME_NUMBERS_10K);
    // const p = getRandomInArray(PRIME_NUMBERS.slice(245, 260));
    this._p = p;
    this.logger.log(`Generating p. p=${this.p}.`);

    return p;
  }


  /**
   * Set a, b
   */
  generateAB(a?: number, b?: number) {
    this.logger.log(`2. [Определение параметров домена] `, 'color:yellow');

    // this.a = a ?? getRandomNumber(101, 599);
    // this.b = b ?? getRandomNumber(101, 599);

    this.a = a ?? getRandomNumber(150, 499);
    this.b = b ?? getRandomNumber(150, 499);

    this.logger.log(`Generating a,b. a=${this.a}, b=${this.b}.`, 'color:yellow');

    this.logger.log(`y${sup(2)}=x${sup(3)} + ax + b`);
    this.logger.log(`y${sup(2)}=x${sup(3)} + ${this.a}x + ${this.b}, E${sub(this.a + ',' + this.b)}(F${sub(this.p)})`);

    return;
  }


  /**
   * A group of points on an elliptic curve
   */
  setM() {
    // https://----------.io/n8EhjAf7HfhUtjBx3hj7yA
    // 07:00
    //
    this.logger.log(`3. [Определение точек эллиптической кривой] `, 'color:yellow');

    this.logger.log(`F${sub(this.p)} =`);

    this.logger.log(`= {1, 2, 3, ..., ${this.p - 1}} = `);
    this.logger.log(`= {±1, ±2, ±3, ..., ±${(this.p - 1) / 2}}`);

    this.logger.log(`\nПоиск всех корней\n`);

    const last = Math.floor((this.p - 1) / 2);

    const gen = this.getGenerator(0, last);

    // these are for shorted logging
    let sliceEnd = Math.ceil(last / 2);
    let sliceStart = sliceEnd - 20;


    const rootsMap = new Map<number, number>();

    if (!this.logLongLists) this.logger.log(` ... \n`);
    while (true) {
      const next = gen.next();
      if (next.done) {
        break;
      }

      const n = next.value ** 2;
      // const h = moduloPositive(n, this.p);

      const [y2] = new LargePowerModulo(next.value, 2, this.p).calc();

      // const hMod = new LargePowerModulo(next.value, 2, this.p);
      // const result = hMod.calc();
      // //const result = hMod.printResults();
      // this.h = result[0];
      // const val = rootsMap.get(h) ?? [];
      // val.push(next.value);

      rootsMap.set(y2, next.value);



      if (next.value === 0) {
        if (this.logLongLists || (sliceStart < next.value && next.value < sliceEnd)) this.logger.log(`${next.value}${sup(2)} = ${n} mod ${this.p} = ${y2}`);
      } else {
        if (this.logLongLists || (sliceStart < next.value && next.value < sliceEnd)) this.logger.log(`(±${next.value})${sup(2)} = ${n} mod ${this.p} = ${y2}`);
      }
      // this.logger.log(`${h}`);

    }
    if (!this.logLongLists) this.logger.log(` ... \n`);

    this.logger.log(``);

    this.logger.log(`Найдено корней: ${rootsMap.size}`);

    this.logger.log(``);

    const points: [number, number][] = [];

    const xGen = this.getGenerator(-(last), last);

    let m: number = 0;

    this.logger.log(`Есть ли корни`);

    while (true) {
      const next = xGen.next();
      if (next.done) {
        break;
      }
      const x = next.value;

      const [x3] = new LargePowerModulo(x, 3, this.p).calc();
      const ax = moduloPositive(this.a * x, this.p);

      // const y2 = x ** 3 + this.a * x + this.b;
      const y2 = x3 + ax + this.b;

      const modY2 = moduloPositive(y2, this.p);

      let color: string;
      if (rootsMap.has(modY2)) {
        // this.logger.log(`${modY2}`, 'color:green');

        //
        if (modY2 === 0) {
          // точка только одна
          m += 1;
        } else {
          // две точки - ±
          m += 2;
        }

        points.push([x, rootsMap.get(modY2)]);

        // const values = rootsMap.get(modY2);
        // for (let i = 0; i < values.length; i++) {
        //   points.push([x, values[i]]);
        // }
      } else {
        color = 'color:gray';
      }

      if (this.logLongLists || next.value <= -last + 20) this.logger.log(`y${sup(2)} = x${sup(3)} + a × x + b = ${x}${sup(3)} + ${this.a} × ${x} + ${this.b} = ${x3} + ${ax} + ${this.b} mod ${this.p} = ${y2} mod ${this.p} = ${modY2}`, color);
    }
    if (!this.logLongLists) this.logger.log(` ... \n`);

    this.E = points.map((p, i) => new Point(p[0], p[1], i));

    this.logger.log(``);
    this.logger.log(`Точки: `);
    for (let i = 0; i < points.length; i++) {
      const point = points[i];
      if (this.logLongLists || i <= 20) this.logger.log(`(${point[0]}, -${point[1]}), (${point[0]}, ${point[1]})`);
    }
    if (!this.logLongLists) this.logger.log(` ... \n`);

    // todo
    m += 1;
    this.logger.log(`Мощность группы`);
    // this.logger.log(` Количество точек ${this.E.length}`);

    this.logger.log(`⏐ E${sub(this.a + ',' + this.b)} (F${sub(this.p)}) ⏐ = m = ${m}`);
    this.logger.log(`m = ${m}`);

    this.m = m;

    return;
  }


  /**
   * q
   */
  generateQ() {
    // https://----------.io/n8EhjAf7HfhUtjBx3hj7yA
    // 20:30
    // 
    // Простое число q - порядок циклической подгруппы группы точек 
    // эллиптической кривой E, m = nq, n ∈ ℕ

    this.logger.log(`4. [Определение q] Простое число q - порядок циклической подгруппы группы точек эллиптической кривой E, m = nq, n ∈ ℕ`, 'color:yellow');

    this.logger.log(`Ограничение m = n × q, где n ∈ ℕ. q - простое число`);

    const factors = primeFactors(this.m).reverse().filter((n, i, a) => a.indexOf(n) === i);

    this.logger.log(`Простые делители m: ${factors}`);

    let n: number = 0;
    let q: number = 0;
    for (let i = 0; i < factors.length; i++) {
      q = factors[i];
      n = this.m / q;
      if (n === Math.floor(n)) {
        break;
      }
    }
    this.q = q;

    // const q = factors[factors.length - 1];
    // this.logger.log(`q = ${q}`);
    //this.q = this.E.length;
    // this.logger.log(`n = m / q =  ${this.m} / ${this.q} = ${n}`);

    if (n !== Math.floor(n)) {
      this.logger.log(`Ошибка ограничение n ∈ ℕ не выполнено (n=${n})`, 'color:red');
    }

    this.logger.log(`q = ${this.q}`);

    return this.q;
  }



  /**
   * Определить точку P
   */
  selectPoint() {
    //
    // Точка P ≠ 0 эллиптический кривой E, 
    // с координатами (x p, y p), удовлетворяющая равенству qP = 0    
    // 

    this.logger.log(`5. [Определить точку] Точка P ≠ 0 эллиптический кривой E, с координатами (x p, y p), удовлетворяющая равенству qP = 0`, 'color:yellow');

    // https://----------.io/n8EhjAf7HfhUtjBx3hj7yA
    // 23:45  
    this.logger.log(`Необходимо в цикле проверять все точки Е пока не найдем точку порядка q\n`);

    // // /// DEBUG
    // const p_1 = new Point(4, 9, 1);
    // const p_2 = this.addPoints(p_1, p_1, 2, true); // 2P = (39, 47)
    // //const p_3 = this.addPoints(p_1, p_2, 3, true); // 3P = (37, 10)
    // const p_3 = this.addPoints(p_2, p_1, 3, true); // 3P = (37, 10)
    // // const p_4 = this.addPoints(p_2, p_2, 4, true); // 4P = (37, -10)
    // // const p_4 = this.addPoints(p_3, p_1, 4, true); // 4P = (37, -10)

    // //const p_7 = this.addPoints(p_3, p_4, 7, true); // 7P = 0

    // this.logger.log(` >>>>>>>>>>>>>>> `);

    // return;



    let foundPoint: Point;


    // ToDo: quick addition check



    for (let eN = 0; eN < this.E.length; eN++) {

      // for (let eN = 31; eN < this.E.length - 25; eN++) {

      const p1 = this.E[eN];

      this.logger.log(`Проверяем точку: ${p1} [${eN}]`, 'color:green');


      let foundPoint = this.calculatePoint(p1, this.q, this.logAddingPoints);
      // const isZero: boolean = this.checkIfZero(p1, this.q, this.logAddingPoints);
      const isZero: boolean = foundPoint.is0;

      if (!!isZero) {
        this.logger.log(`Быстрая проверка показала что точка ${eN}P равна нулю (${isZero}). Продолжаем.`, 'color:cyan');
      } else {
        this.logger.log(`Быстрая проверка показала что точка ${eN}P не равна нулю (${isZero}). Пропускаем.`);
        continue;
      }

      if (p1.y === 0) {
        this.logger.log(`y = 0 . Пропускаем.`);
        continue;
      }

      this.P.clear();
      this.P.set(1, p1);
      this.P.set(this.q, foundPoint);

      if (!this.calculateAllPoints) {
        this.logger.log(``);
        this.logger.log(`Точка найдена: ${p1} [${eN}]`, 'color:blue');
        return;
      }


      let pPrev = p1;

      this.logger.log(`Рассчитываем все точки.`);

      for (let OP = 2; OP <= this.q + 1; OP++) {
        // this.logger.clearLogs();
        this.logger.log(`OP = ${OP}, q=${this.q}`);

        const pNext = this.addPoints(p1, pPrev, OP, this.logAddingPoints);
        // 
        // ================ DEBUG POINT ================
        // const pNext = this.addPoints(p1, pPrev, OP, true);
        // if (OP === 20) return;

        this.P.set(OP, pNext);
        pPrev = pNext;

        if (OP > this.q) {
          this.logger.log(`Порядок точки ${p1}[${eN}] больше q (${this.q}). Не подходит. Переходим к следующей точке.`, 'color:red');
          break;
        }

        if (pNext.is0) {
          this.logger.log(`${OP}P = 0, O(P) = ${OP}`);

          if (OP === this.q) {
            foundPoint = p1;
            this.logger.log(``);
            this.logger.log(`Точка найдена: ${p1} [${eN}]`, 'color:blue');
          }

          break;
        }
      }

      if (foundPoint) {
        this.logger.log(`\n>>>>>>>>>>>>>>>>>> Список всех точек подгруппы ${p1} <<<<<<<<<<<<<<<<<<`);
        for (const k of this.P.keys()) {
          if (this.logLongLists) this.logger.log(`${k}P = ${this.P.get(k)}`);
        }
        if (!this.logLongLists) this.logger.log(`\n \t ... \n`);
        this.logger.log(`Всего точек в подгруппе ${p1}: ${this.P.size}\n`);

        break;
      }

    }

    if (!foundPoint) {
      this.logger.log(` ОШИБКА. ТОЧКА НЕ НАЙДЕНА. `, 'color:red');
    }

    // this.logger.log(`${this.E[31]}`);

    this.logger.log(` `);
    return;
  }


  /**
   * simple hash
   * @returns [hash, sum]
   */
  simpleHashFunction(blocks: number[] = this.inputBlocks) {
    const l = this.l;
    const sum = blocks.reduce((a, c) => a + c, 0);
    const sumMod = moduloPositive(sum, 2 ** l);
    return [sumMod, sum];
  }



  /**
   * Define hash function
   * https://----------.io/n8EhjAf7HfhUtjBx3hj7yA 53-00
   */
  defineHashFunction() {
    this.logger.log(`6. [Задать хеш функцию h()] Сложение блоков длины l по модулю 2${sup('l')} `, 'color:yellow');
    // this.logger.log(`l - битовая длина значения q `);
    this.logger.log(`l - Двоичный логарифм q с окриглением вниз`);

    /**
     * Hash function
     * @param blocks 
     * @returns 
     */
    const func = (blocks: number[] = this.inputBlocks) => {

      // В качестве хэш-функции возьмите сложение блоков сообщения длины  
      // (в двоичном представлении) по модулю 2l

      this.logger.log(`\n`);

      const log2 = Math.floor(Math.log2(this.q));
      this.logger.log(`⌊log₂p⌋ = ⌊log₂${this.q}⌋ = ${log2}`);

      const l = log2;

      const sum = blocks.reduce((a, c) => a + c, 0);
      const hash = moduloPositive(sum, 2 ** l);

      this.logger.log(`hash = ${hash}`);
      this.logger.log(`\n`);

      return [hash, sum];
    };

    this.hashFunction = func;

    this.logger.log(` `);
  }



  /**
   * Ключ подписи - целое число d
   */
  defineD() {

    this.logger.log(`7. [Ключ подписи - целое число d]`, 'color:yellow');
    // https://----------------.io/n8EhjAf7HfhUtjBx3hj7yA
    // 54:30
    // this.d = 3;
    this.d = getRandomNumber(101, 599);

    this.logger.log(`d = ${this.d}`);
    this.logger.log(` `);
  }



  /**
   * Ключ проверки подписи - точка эллиптической кривой Q=dP
   */
  defineQ() {

    this.logger.log(`8. [Ключ проверки подписи - точка эллиптической кривой Q=dP]`, 'color:yellow');
    //
    //this.Q = this.d * this.p;

    this.Q = this.E[3];

    //this.logger.log(` ${this.E[3]} `);
    this.logger.log(`Q = dP = ${this.d}P = ${this.Q}`);
    this.logger.log(` `);

  }



  /**
   * P + P
   * 
   */
  addPoints(
    p1: Point,
    p2: Point,
    pointNumber: number = undefined,
    showLogs: boolean = true,
  ): Point {

    const pN = pointNumber ?? 2;

    if (showLogs) this.logger.log(`\n⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤ `);
    if (showLogs) this.logger.log(`Складываем точки ${p1.toString()} и ${p2.toString()}.`);

    let p: Point;

    if (p1.areMutuallyInverse(p2, this.p)) {
      if (showLogs) this.logger.log(`Точки взаимно обратные. ${pN}P = 0`);
      p = new Point(0, 0);
    } else {
      if (p1.equals(p2)) {
        if (showLogs) this.logger.log(`${pN}P = P + P = ?`);
        p = this.calcAsPplusP(p1, p2, showLogs);
      } else {
        if (showLogs) this.logger.log(`P ≠ Q, Q ≠ -P`);
        p = this.calc3P(p1, p2, showLogs);
      }
    }

    if (showLogs) this.logger.log(`Точка, получившаяся при сложении: ${pN}P = ${p.toString()}`);
    if (showLogs) this.logger.log(`⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤⏤\n`);

    let scalar: number = undefined;
    if (typeof p1.scalar === 'number' && typeof p2.scalar === 'number') {
      scalar = p1.scalar + p2.scalar;
      p.scalar = scalar;
    }
    return p;
  }

  /**
   * Quick check if point is 0
   */
  checkIfZero(p1: Point, order: number, showLogs: boolean = false): boolean {
    const currentPoint = this.calculatePoint(p1, order, showLogs);

    if (currentPoint.is0 && currentPoint.scalar !== order) {

      // we received zero too early
      // this point is not acceptable 



      // Resulting point 5441P (0, 0), true
      // The point is 0 before 5441 5441P (0, 0), true

      if (showLogs) this.logger.log(`\tThe point is 0 before ${order} ${currentPoint.scalar}P ${currentPoint}, ${currentPoint.is0}`, 'color:cyan');

      return false;
    }

    return currentPoint.is0;
  }

  /**
   * Calculate point
   */
  calculatePoint(p1: Point, order: number, showLogs: boolean = false): Point {
    const summands = getAllSummands(order);

    // this.logger.log(`Summands to get ${order} by addition: ${summands.join('+')}`);

    // const pClone = p1.clone();
    // pClone.scalar = 1;

    // const points = new Map<number, Point>([[1, pClone]]);
    // let currentPoint: Point = pClone;

    const points = new Map<number, Point>();
    let currentPoint: Point = undefined;

    // this.logger.log(`Summands: ${summands.join('+')}`);

    for (const summand of summands) {

      if (!currentPoint) {
        const pClone = p1.clone();
        pClone.scalar = 1;
        currentPoint = pClone;
        // this.logger.log(` set scalar ${currentPoint.scalar} `);
        points.set(pClone.scalar, pClone);
        continue;
      }

      // this.logger.log(` getting ${summand} `);

      if (!points.has(summand)) {
        const message = `Point ${summand} does not exist`;
        throw new Error(message);
      }

      const additionPoint = points.get(summand);
      //
      // if (!additionPoint.scalar) {
      //   additionPoint.scalar = 1;
      // }
      //
      // this.logger.log(` scalar ${additionPoint.scalar} `);

      // this.logger.log(`Adding ${currentPoint}(${currentPoint.scalar}) ${additionPoint}(${currentPoint.scalar}) (summand ${summand})`);
      // this.logger.log(` curr ${currentPoint?.scalar}  add  ${additionPoint?.scalar} `);

      currentPoint = this.addPoints(currentPoint, additionPoint, undefined, showLogs);
      if (showLogs) this.logger.log(`\tResulting point ${currentPoint.scalar}P ${currentPoint}, ${currentPoint.is0}`);

      points.set(currentPoint.scalar, currentPoint);

    }

    return currentPoint;
  }



  /**
   * Calc 3P
   * @param p1 
   * @param p2 
   * @returns 
   */
  calc3P(p1: Point, p2: Point, showLogs: boolean = true,): Point {

    if (showLogs) this.logger.log(`x${sub(1)} = ${p1.x}, y${sub(1)} = ${p1.y}, x${sub(2)} = ${p2.x}, y${sub(2)} = ${p2.y}`);
    if (showLogs) this.logger.log(`\n`);

    // calculating x3
    if (showLogs) this.logger.log(`\t ⎛y${sub(2)} - y${sub(1)}⎞${sup(2)}`);
    if (showLogs) this.logger.log(`x${sub(3)} =\t ⎜⎯⎯⎯⎯⎯⎯⎯⎟ - x${sub(1)} - x${sub(2)}`);
    if (showLogs) this.logger.log(`\t ⎝x${sub(2)} - x${sub(1)}⎠`);

    if (showLogs) this.logger.log(`\t ⎛ ${p2.y} - ${p1.y} mod ${this.p} ⎞${sup(2)}`);
    if (showLogs) this.logger.log(`   =\t ⎜⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎟ - ${p1.x} - ${p2.x}`);
    if (showLogs) this.logger.log(`\t ⎝ ${p2.x} - ${p1.x} mod ${this.p} ⎠`);

    // const y2y1 = p2.y - p1.y;
    // const x2x1 = p2.x - p1.x;
    const y2y1 = moduloPositive(p2.y - p1.y, this.p);
    const x2x1 = moduloPositive(p2.x - p1.x, this.p);
    const minusX2x1 = p2.x + p1.x;

    if (showLogs) this.logger.log(`\t ⎛ ${y2y1} ⎞${sup(2)}`);
    if (showLogs) this.logger.log(`   =\t ⎜⎯⎯⎯⎯⎯⎟ - ${minusX2x1}`);
    if (showLogs) this.logger.log(`\t ⎝ ${x2x1} ⎠`);

    const y2y12 = y2y1 ** 2;
    const x2x12 = x2x1 ** 2;

    if (showLogs) this.logger.log(`\t  ${y2y12} mod ${this.p} `);
    if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯ - ${minusX2x1}`);
    if (showLogs) this.logger.log(`\t  ${x2x12} mod ${this.p} `);

    // const y2y12mod = moduloPositive(y2y12, this.p);
    // const x2x12mod = moduloPositive(x2x12, this.p);
    const y2y12mod = y2y12;
    const x2x12mod = x2x12;

    if (showLogs) this.logger.log(`\t  ${y2y12mod} `);
    if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯ - ${minusX2x1}`);
    if (showLogs) this.logger.log(`\t  ${x2x12mod} `);

    if (showLogs) this.logger.log(`\t  ${y2y12mod} - ${x2x12mod} * ${minusX2x1}`);
    if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯ `);
    if (showLogs) this.logger.log(`\t        ${x2x12mod} `);

    const toCommonDivisor = x2x12mod * minusX2x1;

    if (showLogs) this.logger.log(`\t  (${y2y12mod} - ${toCommonDivisor}) mod ${this.p}`);
    if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯ `);
    if (showLogs) this.logger.log(`\t     ${x2x12mod} `);

    const dividend = moduloPositive(y2y12mod - toCommonDivisor, this.p);

    if (showLogs) this.logger.log(`\t     ${dividend}`);
    if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯ `);
    if (showLogs) this.logger.log(`\t     ${x2x12mod} `);

    if (x2x12mod === 0) {
      let scalar: number = undefined;
      if (p1.scalar && p2.scalar) {
        scalar = p1.scalar + p2.scalar;
      }
      if (showLogs) this.logger.log(`${scalar ?? ''}P = 0`, 'color:cyan');
      return new Point(0, 0, scalar);
    }
    const [resultX, e] = divideModulo(dividend, x2x12mod, this.p);

    let x3 = resultX;

    // let e = 0;

    // // hard break
    // let counter = 0;

    // let x3 = dividend / x2x12mod;

    // while (!isInt(x3)) {
    //   e += 1;
    //   const newDividend = dividend + this.p * e;
    //   x3 = newDividend / x2x12mod;

    //   // this.logger.log(`${e} ${x3} ${newDividend}`);

    //   if (counter > 1000) {
    //     this.logger.log(`ERROR: the number of interations is too big (calculating x3).`);
    //     break;
    //   }
    // }

    if (e > 1) {
      if (showLogs) this.logger.log(`\t     ${dividend} + ${this.p} × ${e}`);
      if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯ `);
      if (showLogs) this.logger.log(`\t     ${x2x12mod} `);

      const p_e = multiplyMod(this.p, e, this.p);
      const d = dividend + p_e;
      if (showLogs) this.logger.log(`\t     ${d}`);
      if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯ `);
      if (showLogs) this.logger.log(`\t     ${x2x12mod} `);
    }

    if (showLogs) this.logger.log(`   =\t ${x3}`);
    if (showLogs) this.logger.log(` `);
    if (showLogs) this.logger.log(`x${sub(3)} = ${x3}`, 'color:cyan');
    if (showLogs) this.logger.log(` `);



    // calculating y3

    if (showLogs) this.logger.log(`\t y${sub(2)} - y${sub(1)}`);
    if (showLogs) this.logger.log(`y${sub(3)} =\t ⎯⎯⎯⎯⎯⎯⎯ × (x${sub(1)} - x${sub(3)}) - y${sub(1)}`);
    if (showLogs) this.logger.log(`\t x${sub(2)} - x${sub(1)}`);

    if (showLogs) this.logger.log(`\t ${p2.y} - ${p1.y} mod ${this.p}`);
    if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯ × (${p1.x} - ${x3}) - ${p1.y}`);
    if (showLogs) this.logger.log(`\t ${p2.x} - ${p1.x} mod ${this.p}`);

    // const y2MinusY1 = p2.y - p1.y;
    // const x2MinusX1 = p2.x - p1.x;
    const y2MinusY1 = moduloPositive(p2.y - p1.y, this.p);
    const x2MinusX1 = moduloPositive(p2.x - p1.x, this.p);
    const x1MinusX3 = p1.x - x3;

    if (showLogs) this.logger.log(`\t ${y2MinusY1}`);
    if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯ × ${x1MinusX3} - ${p1.y}`);
    if (showLogs) this.logger.log(`\t ${x2MinusX1}`);

    if (showLogs) this.logger.log(`\t ${y2MinusY1} × ${x1MinusX3}`);
    if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯  - ${p1.y}`);
    if (showLogs) this.logger.log(`\t ${x2MinusX1}`);

    const dividendNew = y2MinusY1 * x1MinusX3;

    if (showLogs) this.logger.log(`\t ${dividendNew} mod ${this.p}`);
    if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  - ${p1.y}`);
    if (showLogs) this.logger.log(`\t ${x2MinusX1}`);

    const dividendNewMod = moduloPositive(dividendNew, this.p);

    if (showLogs) this.logger.log(`\t ${dividendNewMod}`);
    if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯  - ${p1.y}`);
    if (showLogs) this.logger.log(`\t ${x2MinusX1}`);

    if (x2x12mod === 0) {
      let scalar: number = undefined;
      if (p1.scalar && p2.scalar) {
        scalar = p1.scalar + p2.scalar;
      }
      if (showLogs) this.logger.log(`${scalar ?? ''}P = 0`, 'color:cyan');
      return new Point(0, 0, scalar);
    }
    const [resultY, eY] = divideModulo(dividendNewMod, x2MinusX1, this.p);

    let y3 = resultY;

    // let eY = 0;

    // // hard break
    // let counterY = 0;

    // let y3 = dividendNewMod / x2MinusX1;

    // while (!isInt(y3)) {
    //   eY += 1;
    //   const newDividend = dividendNewMod + this.p * eY;
    //   y3 = newDividend / x2MinusX1;

    //   // this.logger.log(`${eY} ${y3} ${newDividend}`);

    //   if (counterY > 1000) {
    //     this.logger.log(`ERROR: the number of interations is too big (calculating y3).`);
    //     break;
    //   }
    // }


    if (eY > 1) {
      if (showLogs) this.logger.log(`\t     ${dividendNewMod} + ${this.p} × ${eY}`);
      if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯ - ${p1.y}`);
      if (showLogs) this.logger.log(`\t     ${x2MinusX1} `);

      if (eY < 10) {
        const p_eY = multiplyMod(this.p, eY, this.p);
        const d = dividend + p_eY;
        if (showLogs) this.logger.log(`\t     ${d}`);
        if (showLogs) this.logger.log(`   =\ ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯ - ${p1.y}`);
        if (showLogs) this.logger.log(`\t     ${x2MinusX1} `);
      }
    }

    if (showLogs) this.logger.log(`   =\t ${y3} - ${p1.y}`);
    y3 -= p1.y;
    y3 = moduloPositive(y3, this.p);

    if (showLogs) this.logger.log(`   =\t ${y3}`);

    if (showLogs) this.logger.log(` `);
    if (showLogs) this.logger.log(`y${sub(3)} = ${y3}`, 'color:cyan');
    if (showLogs) this.logger.log(` `);


    let scalar: number = undefined;
    if (typeof p1.scalar === 'number' && typeof p2.scalar === 'number') {
      scalar = p1.scalar + p2.scalar;
    }
    return new Point(x3, y3, scalar);
  }



  /**
   * Calc as P plus P = 2P
   * @param p1 
   * @param p2 
   * @returns 
   */
  calcAsPplusP(p1: Point, p2: Point, showLogs: boolean = true): Point {

    if (showLogs) this.logger.log(`x${sub(1)} = ${p1.x}, y${sub(1)} = ${p1.y}, x${sub(2)} = ${p2.x}, y${sub(2)} = ${p2.y}`);
    if (showLogs) this.logger.log(`\n`);

    // calculating x3

    if (showLogs) this.logger.log(`\t ⎛3 × x${sub(1)}${sup(2)} + a⎞${sup(2)}`);
    if (showLogs) this.logger.log(`x${sub(3)} =\t ⎜⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎟ - 2 × x${sub(1)}`);
    if (showLogs) this.logger.log(`\t ⎝   2 × y${sub(1)}  ⎠`);

    if (showLogs) this.logger.log(`\t ⎛3 × ${p1.x}${sup(2)} + ${this.a} ⎞${sup(2)}`);
    if (showLogs) this.logger.log(`   =\t ⎜⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎟ - 2 × ${p1.x}`);
    if (showLogs) this.logger.log(`\t ⎝   2 × ${p1.y}   ⎠`);

    const mult2x = 2 * p1.x;

    const [p1x_2] = new LargePowerModulo(p1.x, 2, this.p).calc();
    const p1x_2_3 = multiplyMod(p1x_2, 3, this.p);

    let numerator = p1x_2_3 + this.a;
    // let numerator = 3 * p1.x ** 2 + this.a;
    let denominator = 2 * p1.y;

    if (showLogs) this.logger.log(`\t ⎛ ${numerator} ⎞${sup(2)}`);
    if (showLogs) this.logger.log(`   =\t ⎜⎯⎯⎯⎯⎟ - ${mult2x}`);
    if (showLogs) this.logger.log(`\t ⎝ ${denominator} ⎠`);

    numerator **= 2;
    denominator **= 2;

    if (showLogs) this.logger.log(`\t ⎛ ${numerator} ⎞`);
    if (showLogs) this.logger.log(`   =\t ⎜⎯⎯⎯⎯⎯⎯⎟ - ${mult2x}`);
    if (showLogs) this.logger.log(`\t ⎝ ${denominator}  ⎠`);

    numerator = moduloPositive(numerator, this.p);
    denominator = moduloPositive(denominator, this.p);

    if (showLogs) this.logger.log(`\t ⎛ ${numerator}  ⎞`);
    if (showLogs) this.logger.log(`   =\t ⎜⎯⎯⎯⎯⎯⎟ - ${mult2x}`);
    if (showLogs) this.logger.log(`\t ⎝ ${denominator}  ⎠`);

    // 29-30
    // https://---------.io/n8EhjAf7HfhUtjBx3hj7yA


    if (numerator / denominator !== Math.ceil(numerator / denominator)) {
      const counter = this.findDivisor(numerator, denominator);
      if (showLogs) this.logger.log(`\t ⎛ ${numerator} + ${this.p} × ${counter}  ⎞`);
      if (showLogs) this.logger.log(`   =\t ⎜⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎟ - ${mult2x}`);
      if (showLogs) this.logger.log(`\t ⎝       ${denominator}      ⎠`);

      numerator += this.p * counter;
    }

    if (showLogs) this.logger.log(`\t ⎛ ${numerator}  ⎞`);
    if (showLogs) this.logger.log(`   =\t ⎜⎯⎯⎯⎯⎯⎯⎟ - ${mult2x}`);
    if (showLogs) this.logger.log(`\t ⎝  ${denominator}  ⎠`);

    if (showLogs) this.logger.log(`   =\t ${numerator / denominator} - ${mult2x}`);

    const x3result = numerator / denominator - mult2x;
    // const x3 = moduloPositive(x3result, this.p);
    const [, x3] = modulo2(x3result, this.p);

    if (showLogs) this.logger.log(`   =\t ${x3result} mod ${this.p}`);
    if (showLogs) this.logger.log(`   =\t ${x3}`);

    if (showLogs) this.logger.log(`\n`);

    // calculating y

    if (showLogs) this.logger.log(`\t 3 × x${sub(1)}${sup(2)} + a`);
    if (showLogs) this.logger.log(`y${sub(3)} =\t ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯ × ( x${sub(1)} -  x${sub(3)}) - y${sub(1)}`);
    if (showLogs) this.logger.log(`\t    2 × y${sub(1)}  `);

    if (showLogs) this.logger.log(`\t  3 × ${p1.x}${sup(2)} + ${this.a}`);
    if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯ × (${p1.x} -  ${x3}) - ${p1.y}`);
    if (showLogs) this.logger.log(`\t    2 × ${p1.y}   `);

    let [p1x2] = new LargePowerModulo(p1.x, 2, this.p).calc();
    let p1x2_3 = multiplyMod(p1x2, 3, this.p);
    let numeratorY = p1x2_3 + this.a;

    // let numeratorY = 3 * p1.x ** 2 + this.a;
    let denominatorY = 2 * p1.y;
    const x1x3 = p1.x - x3;

    if (showLogs) this.logger.log(`\t    ${numeratorY}`);
    if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯ × (${x1x3}) - ${p1.y}`);
    if (showLogs) this.logger.log(`\t    ${denominatorY}   `);

    numeratorY *= x1x3;

    if (showLogs) this.logger.log(`\t    ${numeratorY}`);
    if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯ - ${p1.y}`);
    if (showLogs) this.logger.log(`\t    ${denominatorY}   `);

    numeratorY = moduloPositive(numeratorY, this.p);

    if (showLogs) this.logger.log(`\t    ${numeratorY}`);
    if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯ - ${p1.y}`);
    if (showLogs) this.logger.log(`\t    ${denominatorY}   `);

    if (numeratorY / denominatorY !== Math.ceil(numeratorY / denominatorY)) {
      const counter = this.findDivisor(numeratorY, denominatorY);
      if (showLogs) this.logger.log(`\t  ${numeratorY} + ${this.p} × ${counter}  `);
      if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯ - ${p1.y}`);
      if (showLogs) this.logger.log(`\t        ${denominatorY}      `);

      numeratorY += this.p * counter;
    }


    if (showLogs) this.logger.log(`\t    ${numeratorY}`);
    if (showLogs) this.logger.log(`   =\t ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯ - ${p1.y}`);
    if (showLogs) this.logger.log(`\t    ${denominatorY}   `);

    if (showLogs) this.logger.log(`   =\t ${numeratorY / denominatorY} - ${p1.y}`);

    const y3 = moduloPositive(numeratorY / denominatorY - p1.y, this.p);

    if (showLogs) this.logger.log(`   =\t ${y3}`);
    if (showLogs) this.logger.log(`\n`);

    let scalar: number = undefined;
    if (typeof p1.scalar === 'number' && typeof p2.scalar === 'number') {
      scalar = p1.scalar + p2.scalar;

    }
    const p = new Point(x3, y3, scalar);

    return p;
  }



  /**
   * Find 
   */
  findDivisor(n: number, divisor: number): number {

    let result: number = n / divisor;
    let counter: number = 0;
    while (result !== Math.ceil(result)) {
      counter++;
      result = (n + this.p * counter) / divisor;
    }

    return counter;
  }

  /**
   * Get point generator
   */
  getEllipticCurveGenerator(p: number = this.p): Generator<number> {
    const last = (p - 1) / 2;
    return this.getGenerator(1, last);
  }



  /**
   * Get sequence generator
   */
  getGenerator(start: number = 1, end: number = 100): Generator<number> {
    function* func() {
      let index = start;

      while (index <= end) {
        yield index++;
      }
    }
    return func();
  }



  /**
   * Sign the message
   */
  sign(message?: string): string {
    // reset previous signature verification
    this.signatureVerified = null;

    this.logger.log(`Формирование цифровой подписи`, 'color:yellow');
    this.logger.log(`\n`);

    const M = message ?? this.M;

    this.messageToBinMap(M);

    this.setA();


    let br = 0;
    while (this.r === 0 || this.s === 0) {
      br++;
      if (br > 10) {
        throw new Error(`r loop in sign function`);
      }
      // 
      this.setK();
      // step 4
      const r = this.calcR();
      if (r === 0) {
        continue;
      }
      // step 5
      this.calcS();
    }

    // step 6
    const signature = this.calcZ();

    return signature;
  }



  /**
   * Split message into bin and convert to dec
   * 
   */
  messageToBinMap(M: string): number[] {

    this.logger.log('Шаг 1. Конвертируем сообщение М в двоичное представление', 'color:yellow')

    this.logger.log(`Сообщение: ${M}`);

    const plaintextBin = plaintextToBinArray(M).flat().join('');

    this.logger.log(`Полная двоичная последовательность: ${plaintextBin}`);

    this.logger.log(`l - битовая длина числа q`);

    const l = decToBin(this.q).length;
    this.l = l;

    this.logger.log(`Разбиваем на блоки длины l = ${l}`);

    const blocks = slice(plaintextBin, l, true);

    this.logger.log(`Полученные блоки длины l: ${blocks}`);
    this.inputBlocks = blocks.map((s: string) => Number.parseInt(s, 2));
    this.logger.log(`Блоки в десятичном представлении: ${this.inputBlocks}`);
    this.logger.log(`\n`);

    // const plaintextBin = plaintextToBinArray(M).flat().join('');

    return this.inputBlocks;
  }

  /**
   * Split message into bin and convert to dec
   * 
   */
  setA() {
    this.logger.log('Шаг 2. Вычислить целое число а, двоичным представление которого является вектор h и определить e = a (mod q). Если е = 0, то определить е = 1.', 'color:yellow');

    // const sum = this.inputBlocks.reduce((a, c) => a + c, 0);
    // const sumMod = moduloPositive(sum, 2 ** this.l);

    const [sumMod, sum] = this.hashFunction();

    this.signatureA = sumMod;
    this.logger.log(`${this.inputBlocks.join(' + ')} = ${sum} mod 2${sup('l')} = ${sum} mod 2${sup(this.l)} = ${sumMod}`);
    this.logger.log(`a = ${sumMod}`);

    let e = moduloPositive(sumMod, this.q);
    this.logger.log(`e = a mod q = ${this.signatureA} mod ${this.q} = ${e}`);

    if (e !== 0) {
      this.logger.log(`e ≠ 0`);
    } else {
      this.logger.log(`e = 0, значит устанавливаем е =1`);
      e = 1;
    }
    this.logger.log(`e = ${e}`);

    this.signatureE = e;
  }

  /**
   *  
   * Шаг 3
   *
   */
  setK() {
    this.logger.log(`Шаг 3. Сгенерировать случайное целое число k, удовлетворяющее неравенству 0 < k < q`, 'color:yellow');
    // this.logger.log(`Раскомментировать`, 'color:red');
    const k = getRandomNumber(1, this.q - 1);
    this.k = k;

    // calculate this point beforehand
    const p1 = this.P.get(1);
    const pointK = this.calculatePoint(p1, k, true);
    this.P.set(k, pointK);

    // this.k = 3;
    this.logger.log(`k = ${this.k}`);
  }

  /**
   * Шаг 4 r
   */
  calcR() {

    this.logger.log(`Шаг 4. Вычислить точку эллиптической кривой C = kP и определить r = xC (mod q). Если r = 0, то вернуться к шагу 3.`, `color:yellow`);
    const C = this.P.get(this.k);

    if (!C) {
      this.logger.error(`Точки ${this.k}P нет в списке расчитанных точек.`);
    }

    this.logger.log(`C = kP = ${this.k}P = ${C}`);

    const r = moduloPositive(C.x, this.q);
    this.logger.log(`r = x${sub('C')} (mod q) = ${C.x} mod ${this.q} = ${r}`);

    if (r !== 0) {
      this.logger.log(`r ≠ 0`);
      this.logger.log(`r = ${r}`);
    } else {
      this.logger.log(`r = 0, значит переходим к шагу 3`, `color:red`);
    }

    this.r = r;

    return r;
  }

  /**
   * Шаг 5 s
   */
  calcS() {
    this.logger.log(`Шаг 5. Вычислить значение s = (rd + ke) (mod q). Если s = 0, то вернуться к шагу 3.`, `color:yellow`);

    const rd = this.r * this.d;
    const ke = this.k * this.signatureE;
    const rdke = rd + ke;

    const s = moduloPositive(rdke, this.q);

    this.logger.log(`s = (r × d + k × e) mod q = (${this.r} × ${this.d} + ${this.k} × ${this.signatureE}) mod ${this.q}`);
    this.logger.log(`  = (${rd} + ${ke}) mod ${this.q} = ${rdke} mod ${this.q} = ${s}`);

    this.s = s;

    if (s !== 0) {
      this.logger.log(`s ≠ 0`);
      this.logger.log(`s = ${s}`);
    } else {
      this.logger.log(`s = 0, значит переходим к шагу 3`, `color:red`);
    }

    return s;
  }

  /**
   * Шаг
   */
  calcZ() {
    this.logger.log(`Шаг 6. Вычислить двоичные векторы, соответсвующие числас r и s и определить цифровую подпись ζ = r || s как конкатенацию данных двоичных векторов.`, `color:yellow`);

    const rBin = decToBin(this.r, this.l);
    const sBin = decToBin(this.s, this.l);

    const signature = `${rBin}${sBin}`;

    this.logger.log(`r = ${this.r}${sub(10)} = ${rBin}${sub(2)}`);
    this.logger.log(`s = ${this.s}${sub(10)} = ${sBin}${sub(2)}`);
    this.logger.log(`ζ = r || s = ${rBin}${sBin}`);

    this.logger.log(`ЭЦП: ${signature}`, 'color:green');

    this.signature = signature;

    return signature;
  }












  /**
   * Verify signature
   */
  verify(signature?: string): boolean {

    this.logger.log(`Проверка подписи.`, 'color:green');

    if (signature) {
      this.signature = signature;
    }
    this.logger.log(`Подпись: ${this.signature}`, 'color:cyan');

    try {
      this.step1();
      this.step2();
      this.step3();
      this.step4();
      this.step5();
      this.step6();
      this.step7();
    } catch (error) {
      // подпись неверна
      this.logger.log(`================================`, 'color:red');
      this.logger.log(`Проверка подписи: подпись неверна.`, 'color:red');
      this.logger.log(`================================`, 'color:red');

      this.signatureVerified = false;
      return false;
    }

    this.logger.log(`================================`, 'color:blue');
    this.logger.log(`Проверка подписи: подпись верна.`, 'color:blue');
    this.logger.log(`================================`, 'color:blue');

    // this.logger.log(`${this.k}`, 'color:blue');
    this.signatureVerified = true;
    return true;
  }



  /**
   * Step 1
   */
  step1() {
    this.logger.log(`Шаг 1. По полученной подписи ζ вычислить целые числа r и s. Если выполнены неравенства 0 < r < q. 0 < s < q, то перейти к следующему шагу. В противном случае подпись неверна.`, 'color:yellow');

    const vR = this.signature.slice(0, this.l);
    const vS = this.signature.slice(this.l);

    const vRDec = binToDec(vR);
    const vSDec = binToDec(vS);

    this.logger.log(`r = ${vR} = ${vRDec}`);
    this.logger.log(`s = ${vS} = ${vSDec}`);

    if (!(0 < vRDec && vRDec < this.q)) {
      this.logger.log(`r не отвечает условию 0 < r < q`, 'color:red');
      this.logger.log(`Подпись неверна`, 'color:red');
      throw new Error(`Подпись неверна`);
    }

    if (!(0 < vSDec && vSDec < this.q)) {
      this.logger.log(`s не отвечает условию 0 < s < q`, 'color:red');
      this.logger.log(`Подпись неверна`, 'color:red');
      throw new Error(`Подпись неверна`);
    }

    this.vR = vRDec;
    this.vS = vSDec;
    return;
  }

  /**
   * Step 2
   */
  step2() {
    this.logger.log(`Шаг 2. Вычислить хеш - код сообения М : h = h (М)`, 'color:yellow');

    const [hash] = this.hashFunction();
    const hashBin = decToBin(hash);
    this.vHash = hashBin;

    this.logger.log(`h = h(M) = ${hashBin} `, 'color:cyan');

    return;
  }

  /**
   * Step 3
   */
  step3() {
    this.logger.log(`Шаг 3. Вычислить целое число а, двоичным предствалением которого является h, и определить е = а (mod q). Если е = 0, то определить е = 1.`, 'color:yellow');

    const vA = binToDec(this.vHash);
    this.vA = vA;
    this.logger.log(`a = ${this.vA}`);

    let vE = moduloPositive(this.vA, this.q);

    this.logger.log(`e = a mod q = ${this.vA} mod ${this.q} = ${vE}`);

    if (vE === 0) {
      this.logger.log(`e = 0, определяем e = 1 `);
      vE = 1;
    }

    this.vE = vE;
    this.logger.log(`e = ${this.vE}`);

    return;
  }

  /**
   * Step 4
   */
  step4() {
    this.logger.log(`Шаг 4. Вычислить значение v = е⁻¹ (mod q)`, 'color:yellow');

    const alg = new EuclideanAlgorithm(this.q, this.vE);
    const results = alg.calc();
    const [, , eInv] = results;
    const eInverse = moduloPositive(eInv, this.q);
    this.v = eInverse;
    alg.printResults();

    this.logger.log(`Inverse element е⁻¹: ${eInverse}`);
    this.logger.log(`v = е⁻¹ (mod q) = ${this.vE}⁻¹ (mod ${this.q}) = ${this.v}`);


    return;
  }

  /**
   * Step 5
   */
  step5() {
    this.logger.log(`Шаг 5. Вычислить значения z${sub(1)} = sv (mod q), z${sub(2)} = -rv (mod q)`, 'color:yellow');

    const vSq = this.vS * this.v;
    const vSqMod = moduloPositive(vSq, this.q);

    this.logger.log(`Z${sub(1)} = s × v (mod q) = ${this.vS} × ${this.v} mod ${this.q} = ${vSq} mod ${this.q} = ${vSqMod}`);



    const rv = -this.vR * this.v;
    const rvMod = moduloPositive(rv, this.q);

    this.logger.log(`Z${sub(2)} = - r × v (mod q) = ${this.vR} × ${this.v} mod ${this.q} = ${rv} mod ${this.q} = ${rvMod}`);

    const Z1 = vSqMod;
    const Z2 = rvMod;

    this.Z1 = Z1;
    this.Z2 = Z2;

    return;
  }

  /**
   * Step 6
   */
  step6() {
    this.logger.log(`Шаг 6. Вычислить точку эллиптической кривой С = z${sub(1)} Р + z${sub(1)} Q и определить R=хC (mod q).`, 'color:yellow');

    this.logger.log(`Точка Q: ${this.Q}, ${this.d}P`);

    const Z1 = this.Z1;
    const Z2 = this.Z2;

    const P = Z1 + Z2 * this.d;
    const Pmod = moduloPositive(P, this.q);

    const C = this.P.get(Pmod);

    this.logger.log(`C = Z${sub(1)}P + Z${sub(2)}Q = ${Z1}P + ${Z2} × ${this.d}P = ${P}P = ${Pmod}P = ${C}`);
    this.logger.log(`C = ${C}`);

    this.C = C;

    const R = moduloPositive(C.x, this.q);
    this.R = R;

    this.logger.log(`R = x${sub('C')} mod ${this.q} = ${C.x} mod ${this.q} = ${R}`);
    this.logger.log(`R = ${R}`);

    return;
  }

  /**
   * Step 7
   */
  step7() {
    this.logger.log(`Шаг 7. Если выполнено равенство R = r, то подпись принимается, в противном случае, подпись неверна`, 'color:yellow');
    this.logger.log(`Использованные параметры: p=${this.p}, m=${this.m}, a=${this.a}, b=${this.b}, q=${this.q}`, 'color:magenta');
    // this.logger.log(` ${this.E.length} ${this.E.length * 2} `, 'color:magenta');

    if (this.vR !== this.R) {
      throw new Error(`Подпись неверна`);
    }

    return;
  }


  /**
   * Clear logs 
   */
  clearLogs(): void {
    this.logger?.clearLogs();
  }

  // ====================================================================================
  // ====================================================================================
  // ====================================================================================

}
