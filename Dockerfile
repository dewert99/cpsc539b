FROM rustlang/rust:nightly
RUN apt-get update && apt-get install build-essential cmake llvm-dev libclang-dev clang -y --fix-missing --no-install-recommends
WORKDIR /project
COPY . .

RUN cargo install --path .

CMD ["project"]