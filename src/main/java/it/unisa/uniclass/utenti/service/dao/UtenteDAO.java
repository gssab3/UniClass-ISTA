package it.unisa.uniclass.utenti.service.dao;

import it.unisa.uniclass.utenti.model.*;
import jakarta.ejb.Stateless;
import jakarta.persistence.EntityManager;
import jakarta.persistence.NoResultException;
import jakarta.persistence.PersistenceContext;
import jakarta.persistence.TypedQuery;
import java.util.List;

@Stateless(name = "UtenteDAO")
public class UtenteDAO implements UtenteRemote {

    @PersistenceContext(unitName = "DBUniClassPU")
    private EntityManager em;

    @Override
    public void create(Utente utente) {
        em.persist(utente);
    }

    @Override
    public void update(Utente utente) {
        em.merge(utente);
    }

    /**
     * Nota: Aggiunto metodo delete per coerenza con l'interfaccia,
     * se 'delete' non è in UtenteRemote, rinominalo o aggiungilo all'interfaccia.
     */
    public void delete(Utente utente) {
        if (!em.contains(utente)) {
            utente = em.merge(utente);
        }
        em.remove(utente);
    }

    @Override
    public Utente findByEmail(String email) {
        // Usa la named query se vuoi essere esplicito, oppure em.find() se è PK.
        // Qui uso la NamedQuery definita nel passo precedente per coerenza.
        try {
            return em.createNamedQuery("Utente.findByEmail", Utente.class)
                    .setParameter("email", email)
                    .getSingleResult();
        } catch (NoResultException e) {
            return null;
        }
    }

    @Override
    public List<Utente> findAll() {
        return em.createNamedQuery("Utente.findAll", Utente.class)
                .getResultList();
    }

    @Override
    public Utente login(String email, String password) {
        try {
            return em.createNamedQuery("Utente.login", Utente.class)
                    .setParameter("email", email)
                    .setParameter("password", password)
                    .getSingleResult();
        } catch (NoResultException e) {
            return null;
        }
    }

    @Override
    public boolean existsByEmail(String email) {
        Long count = em.createNamedQuery("Utente.checkExists", Long.class)
                .setParameter("email", email)
                .getSingleResult();
        return count > 0;
    }

    // Nota: La named query per "findByTipo" non era definita in Utente.java standard.
    // Se serve, mantieni la query dinamica o aggiungi @NamedQuery in Utente.java
    @Override
    public List<Utente> findByTipo(String tipo) {
        // Questa rimane dinamica a meno che non aggiungi @NamedQuery(name="Utente.findByTipo"...)
        return em.createQuery("SELECT u FROM Utente u WHERE u.Tipo = :tipo", Utente.class)
                .setParameter("tipo", tipo)
                .getResultList();
    }
}