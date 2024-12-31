# Use a base image with necessary C++ tools
FROM gcc:latest


# Install necessary tools, including cmake and LLVM
RUN apt-get update && apt-get install -y \
    build-essential \
    libz3-dev \
    cmake \
    llvm-dev \
    # Add other necessary packages here if needed \
    && rm -rf /var/lib/apt/lists/*
    
# Set the working directory
WORKDIR /relaxinvgen

# Copy the entire project directory into the Docker image
COPY . .

# If needed, configure the project (replace 'build' with your preferred build directory)
RUN mkdir -p build && cd build && cmake .. && cd ..

# Build the project
RUN cd build && make

# Set the entry point to run the compiled application
CMD ["./libMainAnalysis.so"]

