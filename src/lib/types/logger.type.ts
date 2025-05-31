// Basic logger type
export type LoggerType = {
  log: Function;
  warn?: Function;
  error?: Function;
  debug?: Function;

  clearLogs?: Function;
  setVerbosity?: Function;

  logs?: string[];
};

