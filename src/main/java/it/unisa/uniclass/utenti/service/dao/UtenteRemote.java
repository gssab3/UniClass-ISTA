package it.unisa.uniclass.utenti.service.dao;

import it.unisa.uniclass.utenti.model.Utente;
import jakarta.ejb.Remote;
import java.util.List;

@Remote
public interface UtenteRemote {

    //CRUD
     void create(Utente utente);
     void delete(Utente utente);
     void update(Utente utente);

    /**
     * Permette l'autenticazione di un qualsiasi tipo di utente nel sistema.
     * @param email L'email dell'utente.
     * @param password La password (in chiaro o hash, a seconda della policy).
     * @return L'istanza di Utente se le credenziali sono valide, null altrimenti.
     */
    Utente login(String email, String password);

    List<Utente> findByTipo(String tipo);
    Utente findByEmail(String email);

    List<Utente> findAll();

    // Utile per controlli di esistenza pre-registrazione
    boolean existsByEmail(String email);
}
