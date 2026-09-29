#!/usr/bin/env ruby
# frozen_string_literal: true

# Copied from PalomarRegistry/PalomarTemplate (`scripts/validate-formalization.rb`,
# Apache-2.0); unchanged, run from the repository root as
# `ruby scripts/palomar/validate-formalization.rb`.

require "optparse"
require "yaml"

module FormalizationTemplate
  SENTINEL = /\ATEMPLATE(?::|\z)/
  REQUIRED_LICENSE = "Apache-2.0"
  REQUIRED_SECTIONS = %w[project classification automation review].freeze

  class ValidationError < StandardError; end

  def self.load_document(path)
    text = File.binread(path).force_encoding(Encoding::UTF_8)
    raise ValidationError, "#{path} must be valid UTF-8" unless text.valid_encoding?

    document = YAML.safe_load(
      text,
      permitted_classes: [],
      permitted_symbols: [],
      aliases: false
    )
    raise ValidationError, "#{path} must contain one top-level mapping" unless document.is_a?(Hash)

    missing = REQUIRED_SECTIONS.reject { |section| document[section].is_a?(Hash) }
    unless missing.empty?
      raise ValidationError,
            "#{path} must contain the required mapping sections: #{missing.join(', ')}"
    end

    document
  rescue Psych::Exception => error
    detail = error.message.lines.first&.strip
    raise ValidationError, "cannot parse #{path} as YAML: #{detail}"
  rescue SystemCallError => error
    raise ValidationError, "cannot read #{path}: #{error.message}"
  end

  def self.placeholder_paths(value, path = "$")
    case value
    when Hash
      value.flat_map do |key, child|
        placeholder_paths(child, "#{path}.#{key}")
      end
    when Array
      value.each_with_index.flat_map do |child, index|
        placeholder_paths(child, "#{path}[#{index}]")
      end
    when String
      value.lstrip.match?(SENTINEL) ? [path] : []
    else
      []
    end
  end

  def self.validate(path)
    document = load_document(path)
    unless document["version"] == "v0.4"
      raise ValidationError,
            "#{path} $.version must be \"v0.4\", not #{document["version"].inspect}"
    end
    actual_license = document.dig("project", "license")
    unless actual_license == REQUIRED_LICENSE
      raise ValidationError, <<~MESSAGE.chomp
        #{path} $.project.license must be #{REQUIRED_LICENSE.inspect}, not #{actual_license.inspect}.
        Keep the repository's Apache-2.0 LICENSE file unchanged and set project.license to #{REQUIRED_LICENSE.inspect}.
      MESSAGE
    end
    description = document.dig("project", "description")
    unless description.is_a?(String) && !description.strip.empty? && description.strip.length <= 10_000
      raise ValidationError,
            "#{path} $.project.description must be nonempty text of at most 10000 characters"
    end

    placeholders = placeholder_paths(document)
    return placeholders if placeholders.empty?

    locations = placeholders.map { |item| "  #{item}" }.join("\n")
    raise ValidationError, <<~MESSAGE.chomp
      #{path} still contains #{placeholders.length} TEMPLATE value(s):
      #{locations}
      Replace every listed value with project-specific metadata; use [] for a placeholder list where the honest answer is none.
    MESSAGE
  end

  def self.run_cli(arguments, output: $stdout, errors: $stderr)
    parser = OptionParser.new do |options|
      options.banner = "Usage: #{File.basename($PROGRAM_NAME)} [formalization.yaml]"
    end
    remaining = parser.parse(arguments)
    raise OptionParser::InvalidArgument, "expected at most one metadata path" if remaining.length > 1

    path = remaining.fetch(0, "formalization.yaml")
    validate(path)
    output.puts "#{path} contains no TEMPLATE values"
    0
  rescue OptionParser::ParseError => error
    errors.puts error.message
    errors.puts parser
    2
  rescue ValidationError => error
    errors.puts error.message
    1
  end
end

exit FormalizationTemplate.run_cli(ARGV) if $PROGRAM_NAME == __FILE__
