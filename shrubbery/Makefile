OBJECTS=$(patsubst examples/%.shrub, output/%.trieste, $(shell ls examples/*.shrub))
FAILING_OBJECTS=$(patsubst examples/failing/%.shrub, output/failing/%.trieste, $(shell ls examples/failing/*.shrub))

all: build/shrubbery

build/shrubbery: build
	cd build; ninja

build:
	mkdir -p build; cd build; cmake -G Ninja .. -DCMAKE_BUILD_TYPE=Debug -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_CXX_STANDARD=20

output:
	mkdir -p output

output/failing:
	mkdir -p output/failing

output/failing/%.trieste: examples/failing/%.shrub output/failing
	@build/shrubbery build $< -o $@ > /dev/null && echo "Failing test succeeded:" $< || true

output/%.trieste: examples/%.shrub output
	build/shrubbery build $< -o $@

test: $(OBJECTS) $(FAILING_OBJECTS)

clean:
	rm -rf build

.PHONY: clean all build/shrubbery test
