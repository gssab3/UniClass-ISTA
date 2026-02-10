package it.unisa.uniclass.utenti.model;

import jakarta.persistence.*;
import java.io.Serializable;
import java.time.LocalDate;

@Entity
@Table(name = "utente")
@Inheritance(strategy = InheritanceType.JOINED) // Strategia per due tabelle separate
@NamedQueries({
        @NamedQuery(name = "Utente.findAll", query = "SELECT u FROM Utente u"),
        @NamedQuery(name = "Utente.findByEmail", query = "SELECT u FROM Utente u WHERE u.email = :email"),
        @NamedQuery(name = "Utente.checkExists", query = "SELECT count(u) FROM Utente u WHERE u.email = :email"),
        @NamedQuery(name = "Utente.login", query = "SELECT u FROM Utente u WHERE u.email = :email AND u.password = :password"),
        @NamedQuery(name = "Utente.findByTipo", query = "SELECT u FROM Utente u JOIN Accademico a ON u.email = a.email WHERE TYPE(a) = :tipo")
})
public class Utente implements Serializable {

    private static final long serialVersionUID = 1L;

    // --- Attributi comuni a tutti gli utenti ---

    @Id
    @Column(name = "email", nullable = false, length = 100)
    private String email;

    @Column(name = "password", nullable = false)
    private String password;

    @Column(name = "nome", nullable = false)
    private String nome;

    @Column(name = "cognome", nullable = false)
    private String cognome;

    @Column(name = "data_nascita")
    private LocalDate dataNascita;


    @Column(name = "telefono")
    private String telefono;

    @Enumerated(EnumType.STRING)
    @Column(name = "tipo", nullable = false)
    private Tipo tipo;

    @Column(name = "iscrizione") // Data iscrizione account
    private LocalDate iscrizione;


    // --- Costruttori ---


    // Costruttore vuoto richiesto da JPA
    public Utente() {
    }

    public Utente(String email, String password, String nome, String cognome, LocalDate dataNascita, String telefono, LocalDate iscrizione, Tipo tipo) {
        this.email = email;
        this.password = password;
        this.nome = nome;
        this.cognome = cognome;
        this.dataNascita = dataNascita;
        this.telefono = telefono;
        this.iscrizione = iscrizione;
        this.tipo = tipo;
    }

    // --- Getter e Setter ---

    public String getEmail() { return email; }
    public void setEmail(String email) { this.email = email; }

    public String getPassword() { return password; }
    public void setPassword(String password) { this.password = password; }

    public String getNome() { return nome; }
    public void setNome(String nome) { this.nome = nome; }

    public String getCognome() { return cognome; }
    public void setCognome(String cognome) { this.cognome = cognome; }

    public LocalDate getDataNascita() { return dataNascita; }
    public void setDataNascita(LocalDate dataNascita) { this.dataNascita = dataNascita; }

    public String getTelefono() { return telefono; }
    public void setTelefono(String telefono) { this.telefono = telefono; }

    public LocalDate getIscrizione() { return iscrizione; }
    public void setIscrizione(LocalDate iscrizione) { this.iscrizione = iscrizione; }

    public Tipo getTipo() {return tipo;}
    public void setTipo(Tipo tipo) {this.tipo = tipo;}
}