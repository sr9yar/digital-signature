import {
  Gost,
} from './signatures';

const g = new Gost(101);

// console.log('1')

g.sign();
g.verify();



