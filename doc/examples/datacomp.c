

enum D1Tag {
  D1First,
  D1Second,
};

struct D1 {
  enum D1Tag tag;
  union {
    struct {
      const char* asd;
      int kupa;
    } first;

    struct {
      int firstarg;
    } second;
  } content;
};
